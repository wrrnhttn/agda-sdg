{-# OPTIONS --without-K --safe #-}

open import Level hiding (zero)

open import Relation.Binary

module SDG.Extra.OrderedAlgebra.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.Structures
open import Algebra.FunctionProperties

record IsOrderedCommutativeRing
    (_<_ : Rel A ℓ)
    (_+_ _*_ : Op₂ A)
    (-_ : Op₁ A)
    (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
    <-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_
    <-+ : ∀ (a b c) → a < b → (a + c) < (b + c)
    <-* : ∀ (a b) → 0# < a → 0# < b → 0# < (a * b)

  open IsCommutativeRing isCommutativeRing public
    --using (zero)
  open IsStrictTotalOrder <-isStrictTotalOrder public
