{-# OPTIONS --without-K #-}

open import SDG.Extra.OrderedAlgebra

module SDG.SDG {r₁ r₂} (R : OrderedCommutativeRing r₁ r₂) where

open OrderedCommutativeRing R renaming (Carrier to Rc)

open import Data.Product
open import Data.Sum

open import Relation.Binary.Reasoning.Setoid setoid

open import Function using (_$_)

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

-- _⊡_ : (f : ℝ → ℝ) → (g : ℝ → ℝ) → (ℝ → ℝ)
-- f ⊡ g = λ x → f x * g x

--open import Function.Equality
-- open import Relation.Binary.PropositionalEquality
--   renaming (refl to ≡-refl)
-- open ≡-Reasoning
--   renaming (begin_ to ≡-begin_; _∎ to _≡-∎)

open import Algebra.FunctionProperties

-- lemma : ∀ (f : Op₂ Rc) → Congruent₂ f
-- lemma = ?

lemma : ∀ (f : Op₁ Rc) (x : Rc) → f (x + 0#) ≈ f x
lemma f x = {!!} -- how do i do this?!!!

lemma′ : ∀ (f : Rc → Rc) (x : Rc) → gₓ f x d0 ≈ f x
lemma′ f x = {!!}

--open import Function _≈_ _≈_ public

open import Function.Equality
open import Function.Endomorphism.Setoid

--blah : ∀ (f : Rc → Rc) → Congruent f

--blah :  ∀ {x y : Rc} (f : Rc ⟶ Rc) → x ≈ y → f x ≈ f y
-- https://groupprops.subwiki.org/wiki/Congruence_on_an_algebra
postulate -- IS THIS NECESSARY? BAD!!!
  ≈-cong : ∀ (f : Rc → Rc) {x y : Rc} → x ≈ y → f x ≈ f y
--≈-cong f {x} {y} x≈y = {!begin f x ≈⟨ f (begin ?) ⟩ ? ∎!}


-- "the fundamental equation of the differential calculus in 𝕊" (bell)
-- aka taylor's formula
taylors : ∀ (f : Rc → Rc) (x : Rc) (d : D) → (f (x + (D→R d))) ≈ (f x) + ((D→R d) * ((f ′) x))
taylors f x d = begin
    f (x + D→R d)                   ≈⟨ refl ⟩
    gₓ f x d                        ≈⟨ bprop d ⟩
    (gₓ f x d0) + (D→R d * (f ′) x) ≈⟨ refl ⟩
    f (x + 0#) + (D→R d * (f ′) x)  ≈⟨ +-congʳ $ ≈-cong f $ +-identityʳ _ ⟩
    f x + (D→R d * (f ′) x)         ∎
  where
    bprop = proj₁ (proj₂ (∃!b f x))
    -- f≈ = ≡-begin 
    --   f (x + 0#) ≡-Reasoning.≡⟨ {!cong f $ +-identityʳ!} ⟩ {!!}

_⊞_ : (f : Rc → Rc) → (g : Rc → Rc) → (Rc → Rc)
f ⊞ g = λ x → f x + g x

sum-rule : ∀ (f g : Rc → Rc) (x : Rc)  → ((f ⊞ g) ′) x ≈ ((f ′) ⊞ (g ′)) x
sum-rule f g x = 
  begin 
    ((f ⊞ g) ′) x     ≈⟨ refl ⟩
    b                 ≈⟨ b≈ggf′+g′ ⟩
    ((f ′) ⊞ (g ′)) x ∎
  where
   gg : D → Rc
   gg = λ d → (f ⊞ g) (x + D→R d)
   b = proj₁ (kock-lawvere gg)
   unique : ∀ {y} → (∀ (d : D) → gg d ≈ (gg d0) + ((D→R d) * y)) → b ≈ y
   unique = proj₂ (proj₂ (kock-lawvere gg))
   ggf′+g′ : ∀ (d : D) → gg d ≈ (gg d0) + ((D→R d) * (((f ′) ⊞ (g ′)) x))
   ggf′+g′ d =
     begin 
       (f (x + D→R d)) + (g (x + D→R d))           ≈⟨ +-congʳ $ taylors f x d ⟩ 
       (f x + (D→R d * (f ′) x)) + (g (x + D→R d)) ≈⟨  +-congˡ $ taylors g x d ⟩ 
       (f x + (D→R d * (f ′) x)) + (g x + (D→R d * (g ′) x)) ≈⟨ +-assoc _ _ _ ⟩
       f x + ((D→R d * (f ′) x) + (g x + (D→R d * (g ′) x))) ≈⟨ +-congˡ $ sym $ +-assoc _ _ _ ⟩
       f x + (((D→R d * (f ′) x) + g x) + (D→R d * (g ′) x)) ≈⟨ +-congˡ $ +-congʳ $ +-comm _ _ ⟩
       f x + ((g x + (D→R d * (f ′) x)) + (D→R d * (g ′) x)) ≈⟨ +-congˡ $ +-assoc _ _ _ ⟩
       f x + (g x + ((D→R d * (f ′) x) + (D→R d * (g ′) x))) ≈⟨ sym $ +-assoc _ _ _ ⟩
       (f x + g x) + ((D→R d * (f ′) x) + (D→R d * (g ′) x)) ≈⟨ +-congˡ $ sym $ distribˡ _ _ _ ⟩
       (f x + g x) + D→R d * ((f ′) x + (g ′) x) ≈⟨ refl ⟩
       (f ⊞ g) x + D→R d * ((f ′) ⊞ (g ′)) x  ≈⟨ +-congʳ $ ≈-cong (f ⊞ g) $ sym $ +-identityʳ _  ⟩
       gg d0 + D→R d * ((f ′) ⊞ (g ′)) x ∎
   b≈ggf′+g′ : b ≈ ((f ′) ⊞ (g ′)) x
   b≈ggf′+g′ = unique ggf′+g′
   
