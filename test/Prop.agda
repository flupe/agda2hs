{-# OPTIONS --prop #-}
module Prop where

open import Haskell.Prelude
open import Haskell.Prim using (itsTrue)

data Squash (A : Set) : Prop where
  [_] : A → Squash A

record Refinement (A : Set) (@0 P : @0 A → Prop) : Set where
  constructor _⟨_⟩
  field
    value : A
    proof : P value
{-# COMPILE AGDA2HS Refinement unboxed #-}

_⟨⟩ : ∀ {A : Set} {P : A → Prop}
   → {x y : A} → x ≡ y
   → {p : P x} {q : P y}
   → x ⟨ p ⟩ ≡ y ⟨ q ⟩
refl ⟨⟩ = refl

record Box (A : Set) (@0 P : @0 A → Set) : Set where
  constructor _⟦_⟧
  field
    value : A
    proof : Squash (P value)
{-# COMPILE AGDA2HS Box unboxed #-}

test : Box Nat (λ x → IsTrue (x >= 3))
test = 4 ⟦ [ itsTrue ] ⟧

{-# COMPILE AGDA2HS test #-}
