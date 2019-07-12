{-# OPTIONS --without-K #-}

open import SDG.Extra.OrderedAlgebra

module SDG.SDG {r₁ r₂} (R : OrderedCommutativeRing r₁ r₂) where

open OrderedCommutativeRing R renaming (Carrier to Rc)

open import Data.Product
open import Data.Sum

open import Algebra

-- note: SDG should probably be a record if i need to
--       use some particular topos model

--nilsqr : {!!}
nilsqr = λ x → (x * x) ≈ 0#

nilsqr-0# : nilsqr 0#
nilsqr-0# = zeroˡ 0#

--D : {!!}
D = Σ[ x ∈ Rc ] (nilsqr x)

D→R : D → Rc
D→R d = proj₁ d

R→D : (x : Rc) → nilsqr x → D
R→D x nilsqr = x , nilsqr

d0 : D
d0 = R→D 0# nilsqr-0#

postulate
  kock-lawvere : ∀ (g : D → Rc) →
                   ∃! _≈_ (λ b → ∀ (d : D) → ((g d) ≈ ((g d0) + (D→R d * b))))

-- these definitions are modified from previous development based on Bell:

gₓ : ∀ (f : Rc → Rc) (x : Rc) → (D → Rc)
gₓ f x d = f (x + D→R d)

∃!b : ∀ (f : Rc → Rc) (x : Rc) → ∃! _≈_ (λ b → ∀ (d : D) → ((gₓ f x d) ≈ ((gₓ f x d0) + (D→R d * b))))
∃!b f x = kock-lawvere (gₓ f x)

_′ : (f : Rc → Rc) → (Rc → Rc)
(f ′) x = proj₁ (∃!b f x)
