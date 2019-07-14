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

--open import Function.Congruent _≈_ _≈_ public

--blah : ∀ (f : Rc → Rc) → Congruent f

≈-cong : ∀ (f : Rc → Rc) {x y} → x ≈ y → f x ≈ f y
≈-cong f x≈y = {!!}

-- "the fundamental equation of the differential calculus in 𝕊" (bell)
-- aka taylor's formula
taylors : ∀ (f : Rc → Rc) (x : Rc) (d : D) → (f (x + (D→R d))) ≈ (f x) + ((D→R d) * ((f ′) x))
taylors f x d = begin
    f (x + D→R d)                   ≈⟨ refl ⟩
    gₓ f x d                        ≈⟨ bprop d ⟩
    (gₓ f x d0) + (D→R d * (f ′) x) ≈⟨ refl ⟩
    f (x + 0#) + (D→R d * (f ′) x)  ≈⟨ +-congʳ $ {!!} ⟩
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
   gg = λ e → (f ⊞ g) (x + D→R e)
   b = proj₁ (kock-lawvere gg)
   unique : ∀ {y} → (∀ (e : D) → gg e ≈ (gg d0) + ((D→R e) * y)) → b ≈ y
   unique = proj₂ (proj₂ (kock-lawvere gg))
   ggf′+g′ : ∀ (d : D) → gg d ≈ (gg d0) + ((D→R d) * (((f ′) ⊞ (g ′)) x))
   ggf′+g′ d =
     begin 
       (f (x + D→R d)) + (g (x + D→R d))           ≈⟨ +-congʳ $ taylors f x d ⟩ 
       (f x + (D→R d * (f ′) x)) + (g (x + D→R d)) ≈⟨  +-congˡ $ taylors g x d ⟩ 
       (f x + (D→R d * (f ′) x)) + (g x + (D→R d * (g ′) x)) ≈⟨ {!!} ⟩ 
       (f x + g x) + ((D→R d * (f ′) x) + (D→R d * (g ′) x)) ≈⟨ +-congˡ $ sym $ distribˡ _ _ _ ⟩
       (f x + g x) + D→R d * ((f ′) x + (g ′) x) ≈⟨ refl ⟩
       (f ⊞ g) x + D→R d * ((f ′) ⊞ (g ′)) x  ≈⟨ {!!} ⟩
       gg d0 + D→R d * ((f ′) ⊞ (g ′)) x ∎
   b≈ggf′+g′ : b ≈ ((f ′) ⊞ (g ′)) x
   b≈ggf′+g′ = unique ggf′+g′


  -- kock-lawvere : ∀ (g : D → Rc) →
  --                  ∃! _≈_ (λ b → ∀ (d : D) → ((g d) ≈ ((g d0) + (D→R d * b))))

-- sum-rule : ∀ (f g : Rc → Rc) (x : Rc) → ((f ⊞ g) ′) x ≈ ((f ′) ⊞ (g ′)) x
-- sum-rule f g x =
--    ((f ⊞ g) ′) x
--   ≡⟨⟩ 
--     b
 --  ≡⟨  b≡ggf′+g′ ⟩ 
 --    ((f ′) ⊞ (g ′)) x
 --  ∎
 -- where
 --  gg : D → Rc
 --  gg = λ e → (f ⊞ g) (x + R→D e)
 --  b = proj₁ (kock-lawvere gg)
 --  unique : ∀ {y} → (∀ (e : D) → gg e ≈ (gg d0) + (y * (R→D e))) → b ≈ y
 --  unique = proj₂ (proj₂ (kock-lawvere gg))
 --  ggprop = proj₁ (proj₂ (kock-lawvere gg))
 --  ggf′+g′ : ∀ (e : D) → gg e ≈ (gg d0) + ((((f ′) ⊞ (g ′)) x) * (R→D e))
 --  ggf′+g′ e = begin
 --      gg e
 --    ≈⟨ refl ⟩ 
 --      (f (x + R→D e)) + (g (x + R→D e))
 --    ≈⟨ cong (λ y → y + (g (x + ε e))) (fun-diff-eqn f x e) ⟩
 --      (f x + (ε e * (f ′) x)) + (g (x + ε e))
 --    ≡⟨ cong (λ y → (f x + (ε e * (f ′) x)) + y) (fun-diff-eqn g x e) ⟩
 --      (f x + (ε e * (f ′) x)) + (g x + (ε e * (g ′) x))
 --    ≡⟨ +-assoc (f x) (ε e * (f ′) x) (g x + (ε e * (g ′) x)) ⟩
 --      (f x) + ((ε e * (f ′) x) + (g x + (ε e * (g ′) x)))
 --    ≡⟨ cong (λ y → (f x) + y) (sym (+-assoc (ε e * (f ′) x) (g x) (ε e * (g ′) x))) ⟩
 --      (f x) + (((ε e * (f ′) x) + g x) + (ε e * (g ′) x))
 --    ≡⟨ cong (λ y → (f x) + (y + (ε e * (g ′) x))) (+-comm (ε e * (f ′) x) (g x)) ⟩
 --      (f x) + ((g x + (ε e * (f ′) x)) + (ε e * (g ′) x))
 --    ≡⟨ cong (λ y → (f x) + y) (+-assoc (g x) (ε e * (f ′) x) (ε e * (g ′) x)) ⟩
 --       ((f x) + (g x + (((ε e * (f ′) x)) + (ε e * (g ′) x))))
 --    ≡⟨ sym (+-assoc (f x) (g x) ((ε e * (f ′) x) + (ε e * (g ′) x))) ⟩
 --      (f x + g x) + ((ε e * (f ′) x) + (ε e * (g ′) x))
 --    ≡⟨ cong (λ y → (f ⊞ g) x + y) (sym (*-+-distr (ε e) ((f ′) x) ((g ′) x))) ⟩ 
 --      (f ⊞ g) x + ((ε e) * (((f ′) ⊞ (g ′)) x))
 --    ≡⟨ cong (λ y → (f ⊞ g) x + y) (*-comm (ε e) (((f ′) ⊞ (g ′)) x)) ⟩ 
 --      (f ⊞ g) x + (((f ′) ⊞ (g ′)) x * ε e)
 --    ≡⟨ cong (λ y → (f ⊞ g) y + (((f ′) ⊞ (g ′)) x * ε e)) (sym (+-identityʳ x)) ⟩ 
 --      (f ⊞ g) (x + r₀) + (((f ′) ⊞ (g ′)) x * ε e)
 --    ≡⟨⟩
 --      gg δr₀ + (((f ′) ⊞ (g ′)) x * ε e)
 --    ∎
 --  b≡ggf′+g′ : b ≡ ((f ′) ⊞ (g ′)) x
 --  b≡ggf′+g′ = unique ggf′+g′
