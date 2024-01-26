{-# LANGUAGE OverloadedStrings #-}
module Agda2Hs.Render where

import Control.Monad ( unless )
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import Data.Foldable ( fold )
import Data.Function ( on )
import Data.List ( sortBy, nub, isPrefixOf, intercalate, intersperse )
import Data.Maybe ( fromMaybe, isNothing )
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified Data.Text.Lazy.IO      as Text ( writeFile )
import qualified Data.Text.Lazy.Builder as Text

import System.FilePath ( takeDirectory, (</>) )
import System.Directory ( createDirectoryIfMissing )

import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curIF, compileDir )

import Agda.TypeChecking.Pretty
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.Compile
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Imports
import Agda2Hs.Compile.Utils ( primModules )
import Agda2Hs.HsUtils
import Agda2Hs.Pragma ( getForeignPragmas )

import Language.Haskell.Exts as Hs (prettyPrint, prelude_mod)

-- Rendering --------------------------------------------------------------

type Block = Ranged Text.Builder

sortRanges :: [Ranged a] -> [a]
sortRanges = map snd . sortBy (compare `on` rLine . fst)

rLine :: Range -> Int
rLine r = fromIntegral $ fromMaybe 0 $ posLine <$> rStart r

renderBlocks :: [Block] -> Text.Builder
renderBlocks = unlinesB . sortRanges

unlinesB :: [Text.Builder] -> Text.Builder
unlinesB = foldMap (<> "\n")

defBlock :: [Ranged [Hs.Decl ()]] -> [Block]
defBlock def = [ (r, unlinesB $ map (pp . insertParens) ds) | (r, ds) <- def ]

renderLangExts :: [Hs.KnownExtension] -> Text.Builder
renderLangExts exts
  | null exts = mempty
  | otherwise = pp (Hs.LanguagePragma () $ nub $ map extToName exts) <> "\n"

codePragmas :: [Ranged Code] -> [Block]
codePragmas code = [ (r, unlinesB $ map pp ps) | (r, (Hs.Module _ _ ps _ _, _)) <- code, not (null ps) ]

codeBlocks :: [Ranged Code] -> [Block]
codeBlocks code = [(r, Text.fromString (uncurry Hs.exactPrint $ moveToTop $ noPragmas mcs) <> "\n") | (r, mcs) <- code, nonempty mcs]
  where noPragmas (Hs.Module l h _ is ds, cs) = (Hs.Module l h [] is ds, cs)
        noPragmas m                          = m
        nonempty (Hs.Module _ _ _ is ds, cs) = not $ null is && null ds && null cs
        nonempty _                           = True

-- Generating the files -------------------------------------------------------

moduleFileName :: Options -> TopLevelModuleName -> TCM FilePath
moduleFileName opts name = do
  outDir <- compileDir
  return $ fromMaybe outDir (optOutDir opts) </> moduleNameToFileName name "hs"

-- NOTE: what does this have to do with rendering?
moduleSetup :: Options -> IsMain -> TopLevelModuleName -> Maybe FilePath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup _ _ m _ = do
  -- we never compile primitive modules
  if any (`isPrefixOf` prettyShow m) primModules then pure $ Skip ()
  else do
    reportSDoc "agda2hs.compile" 3 $ text "Compiling module: " <+> prettyTCM m
    setScope . iInsideScope =<< curIF
    return $ Recompile m

ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

-- NOTE(flupe): this is horrendous and should be rewritten asap
--
-- We have to rewrite this so that in the IThingAll and IThingWith import specs,
-- the "type" prefixes get before type operators if necessary.
-- But see haskell-src-exts, PR #475. If it gets merged, this will be unnecessary.
prettyShowImportDecl :: Hs.ImportDecl () -> Text.Builder
prettyShowImportDecl (Hs.ImportDecl _ m qual src safe mbPkg mbName mbSpecs) =
  ("import " <>) $
  (if src  then ("{-# SOURCE #-} " <>) else id) $
  (if safe then ("safe " <>) else id) $
  (if qual then ("qualified " <>) else id) $
  maybeAppend (Text.fromString . show) mbPkg $
  (pp m <>) $
  maybeAppend (\m' -> " as " <> pp m') mbName $
  maybe mempty ((" " <>) . prettyShowSpecList) mbSpecs
    where
      maybeAppend :: (a -> Text.Builder) -> Maybe a -> Text.Builder -> Text.Builder
      maybeAppend f (Just a) = (f a <>)
      maybeAppend _ Nothing  = id

      prettyShowSpecList :: Hs.ImportSpecList () -> Text.Builder
      prettyShowSpecList (Hs.ImportSpecList _ b ispecs)  =
        (if b then "hiding " else "") <> parenList (map prettyShowSpec ispecs)

      -- this is why we have rewritten it
      prettyShowSpec :: Hs.ImportSpec () -> Text.Builder
      prettyShowSpec (Hs.IVar _ name   )  = pp name
      prettyShowSpec (Hs.IAbs _ ns name) | Hs.TypeNamespace () <- ns = pp ns <> " " <> pp name
                                         | otherwise                 = pp name

      prettyShowSpec (Hs.IThingAll _ name) =
        let rest = pp name <> "(..)" in
        case name of
          -- if it's a symbol, append a "type" prefix to the beginning
          (Hs.Symbol _ _) -> pp (Hs.TypeNamespace ()) <> (" " <> rest)
          (Hs.Ident  _ _) -> rest

      prettyShowSpec (Hs.IThingWith _ name nameList) =
        let rest = pp name <> (parenList . map pp $ nameList) in
        case name of
          (Hs.Symbol _ _) -> pp (Hs.TypeNamespace ()) <> (" " <> rest)
          (Hs.Ident  _ _) -> rest

      parenList :: [Text.Builder] -> Text.Builder
      parenList xs = "(" <> fold (intersperse ", " xs) <> ")"


writeModule :: Options -> ModuleEnv -> IsMain -> TopLevelModuleName
            -> [(CompiledDef, CompileOutput)] -> TCM ModuleRes
writeModule opts _ isMain m outs = do
  code <- getForeignPragmas (optExtensions opts)

  let mod  = prettyShow m
      (cdefs, impss, extss) = unzip3 $ flip map outs $
        \(cdef, CompileOutput imps exts) -> (cdef, imps, exts)
      defs = concatMap defBlock cdefs ++ codeBlocks code
      imps = concat impss
      exts = concat extss

  unless (null code && null defs && isMain == NotMain) $ do

    let unlines' [] = []
        unlines' ss = unlines ss ++ "\n"

    let preOpts@PreludeOpts{..} = optPrelude opts

    -- if the prelude is supposed to be implicit,
    -- or the prelude imports have been fixed in the config file,
    -- we remove it from the list of imports
    let filteredImps =
          if not preludeImplicit && isNothing preludeImports
            then imps
            else filter ((/= Hs.prelude_mod ()) . importModule) imps

    -- then we try to add it back
    autoImportList <-
      if (not preludeImplicit && isNothing preludeImports) || null preludeHiding
        then compileImports mod filteredImps
        else (preludeImportDecl preOpts:) <$> compileImports mod filteredImps

    -- Add automatic imports
    let autoImports =
          if null autoImportList
            then mempty
            else unlinesB (fmap prettyShowImportDecl autoImportList) <> "\n"

    -- The comments make it hard to generate and pretty print a full module
    hsFile <- moduleFileName opts m

    let output = Text.toLazyText $ fold
          [ renderLangExts exts
          , renderBlocks $ codePragmas code
          , "module " <> (Text.fromString mod <> " where\n\n")
          , autoImports
          , renderBlocks defs
          ]

    reportSLn "" 1 $ "Writing " ++ hsFile

    liftIO $ ensureDirectory hsFile >> Text.writeFile hsFile output
