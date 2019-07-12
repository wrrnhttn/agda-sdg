{-# OPTIONS --without-K --safe #-}

module SDG.Extra.OrderedAlgebra where

open import Relation.Binary
open import Algebra.FunctionProperties
open import Level

open import SDG.Extra.OrderedAlgebra.Structures

record OrderedCommutativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix 4 _≈_
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _<_ : Rel Carrier ℓ
    _+_ : Op₂ Carrier
    _*_ : Op₂ Carrier
    -_ : Op₁ Carrier
    0# : Carrier
    1# : Carrier
    isOrderedCommutativeRing : IsOrderedCommutativeRing _≈_ _<_ _+_ _*_ -_ 1# 0#
