module Haskell.Extra.Erase where

  open import Agda.Primitive
  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Equality
  open import Haskell.Prim
  open import Haskell.Prim.List

  private variable 
    @0 x y : a
    @0 xs  : List a

  record Erase (@0 a : Set ℓ) : Set ℓ where
    constructor Erased
    field @0 get : a
  open Erase public

  infixr 4 ⟨_⟩_
  record Σ0 (@0 a : Set) (b : @0 a → Set) : Set where
    constructor ⟨_⟩_
    field
      @0 proj₁ : a
      proj₂ : b proj₁
  open Σ0 public
  {-# COMPILE AGDA2HS Σ0 unboxed #-}

  pattern <_> x = record { proj₁ = _ ; proj₂ = x }

  -- Resurrection of erased values
  record Rezz (a : Set ℓ) (@0 x : a) : Set ℓ where
    constructor Rezzed
    field
      rezzed    : a
      @0 isRezz : rezzed ≡ x
  open Rezz public
  {-# COMPILE AGDA2HS Rezz unboxed #-}

  pattern rezz x = Rezzed x refl

  instance
    rezz-id : {x : a} → Rezz a x
    rezz-id = rezz _

  private
    @0 cong : (f : a → b) {x y : a} → x ≡ y → f x ≡ f y
    cong f refl = refl

    @0 cong2 : (f : a → b → c) {x y : a} {z w : b}
             → x ≡ y → z ≡ w → f x z ≡ f y w
    cong2 f refl refl = refl

    @0 subst : {p : a → Set} {x y : a} → x ≡ y → p x → p y
    subst refl t = t

    @0 sym : {x y : a} → x ≡ y → y ≡ x
    sym refl = refl

  rezzCong : {@0 x : a} (f : a → b) → Rezz a x → Rezz b (f x)
  rezzCong f (Rezzed x p) = Rezzed (f x) (cong f p)
  {-# COMPILE AGDA2HS rezzCong inline #-}

  rezzCong2 : (f : a → b → c) → Rezz a x → Rezz b y → Rezz c (f x y)
  rezzCong2 f (Rezzed x p) (Rezzed y q) = Rezzed (f x y) (cong2 f p q)
  {-# COMPILE AGDA2HS rezzCong2 inline #-}

  rezzHead : Rezz (List a) (x ∷ xs) → Rezz a x
  rezzHead (Rezzed xs p) =
    Rezzed
      (head xs ⦃ subst {p = NonEmpty} (sym p) itsNonEmpty ⦄)
      (subst {p = λ xs → ⦃ @0 _ : NonEmpty xs ⦄ → head xs ≡ _} (sym p) refl
        ⦃ subst {p = NonEmpty} (sym p) itsNonEmpty ⦄)
  {-# COMPILE AGDA2HS rezzHead inline #-}

  rezzTail : Rezz (List a) (x ∷ xs) → Rezz (List a) xs
  rezzTail (Rezzed xs p) =
    Rezzed
      (tail xs ⦃ subst {p = NonEmpty} (sym p) itsNonEmpty ⦄)
      (subst {p = λ xs → ⦃ @0 _ : NonEmpty xs ⦄ → tail xs ≡ _} (sym p) refl
        ⦃ subst {p = NonEmpty} (sym p) itsNonEmpty ⦄)
  {-# COMPILE AGDA2HS rezzTail inline #-}

  rezzErase : Rezz (Erase a) (Erased x)
  rezzErase {x = x} = Rezzed (Erased x) refl

  erase-injective : Erased x ≡ Erased y → x ≡ y
  erase-injective refl = refl

  inspect_by_ : (x : a) → (Rezz a x → b) → b
  inspect x by f = f (rezz x)
