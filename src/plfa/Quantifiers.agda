module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_) -- renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.Isomorphism using (_≃_; extensionality)
open import plfa.Induction using (+-rearrange; +-comm; +-suc; +-identityʳ; +-assoc)
open import plfa.Equality using (≡-implies-≤; +-monoˡ-≤)
open import plfa.Induction using (Bin; inc; to; from; from-to)
open import plfa.Relations using (Can; One; to-from; to-can)


∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- Exercise ∀-distrib-×

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ f → ( (λ a → proj₁ (f a)) , (λ a → proj₂ (f a)) )
    ; from = λ{ (g , h) → λ a → (g a) , (h a) }
    ; from∘to = λ f → refl
    ; to∘from = λ{ (g , h) → refl }
    }

-- Exercise ⊎∀-implies-∀⊎

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x) = λ a → inj₁ (x a)
⊎∀-implies-∀⊎ (inj₂ y) = λ a → inj₂ (y a)

-- -- the converse not stands, consider A = {1, 2}, explanation:
-- -- B 1 B 2 C 1 C 2
-- -- ---------------
-- --  1   0   0   1

-- Exercise ∀-×

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- extensionality doesn't satisfy this
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ x → f x ≡ g x)
      -----------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× {B} =
  record
    { to = λ f → (f aa) , (f bb) , (f cc)
    ; from = λ{ (a , b , c) → λ{ aa → a ; bb → b ; cc → c } }
    ; from∘to = λ f → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ{ (a , b , c) → refl }
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to = λ f → λ{ ⟨ x , y ⟩ → f x y}
    ; from = λ f a bx → f ⟨ a , bx ⟩
    ; from∘to = λ x → refl
    ; to∘from = λ f → extensionality λ{ ⟨ x , y ⟩ → refl }
    }

-- Exercise ∃-distrib-⊎

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{ ⟨ x , inj₁ bx ⟩ → inj₁ ⟨ x , bx ⟩ ; ⟨ x , inj₂ cx ⟩ → inj₂ ⟨ x , cx ⟩ }
    ; from = λ { (inj₁ ⟨ x , y ⟩) → ⟨ x , (inj₁ y) ⟩ ; (inj₂ ⟨ x , y ⟩) → ⟨ x , (inj₂ y) ⟩ }
    ; from∘to = λ{ ⟨ x , inj₁ y ⟩ → refl ; ⟨ x , inj₂ y ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , y ⟩) → refl ; (inj₂ ⟨ x , y ⟩) → refl }
    }

-- Exercise ∃×-implies-×∃

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , (bx , cx) ⟩ = ⟨ a , bx ⟩ , ⟨ a , cx ⟩

-- Exercise ∃-⊎

∃-⊎ : ∀ {B : Tri → Set}
  → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to = λ{ ⟨ aa , y ⟩ → inj₁ y ; ⟨ bb , y ⟩ → inj₂ (inj₁ y) ; ⟨ cc , y ⟩ → inj₂ (inj₂ y) }
    ; from = λ { (inj₁ x) → ⟨ aa , x ⟩ ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩ ; (inj₂ (inj₂ x)) → ⟨ cc , x ⟩ }
    ; from∘to = λ{ ⟨ aa , y ⟩ → refl ; ⟨ bb , y ⟩ → refl ; ⟨ cc , y ⟩ → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ x)) → refl }
    }

-- Definition of even & odd --

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- - --

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc x) with odd-∃ x
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc x) with even-∃ x
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc x , refl ⟩ = even-suc (∃-odd ⟨ x , refl ⟩)

∃-odd ⟨ x , refl ⟩ = odd-suc (∃-even ⟨ x , refl ⟩)

-- Exercise ∃-even-odd

-- - I have no idea why it says "Termination checking failed" ;-;

-- ∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
-- ∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n
--
-- ∃-even′ ⟨ zero , refl ⟩ = even-zero
-- ∃-even′ ⟨ suc x , refl ⟩ = even-suc (∃-odd′ ⟨ x , lemma ⟩)
--   where
--     lemma : ∀ {x : ℕ} → x + (x + zero) + 1 ≡ x + suc (x + zero)
--     lemma {x} rewrite sym (+-rearrange x x 0 1)
--               | +-comm (x + x) 1
--               | +-identityʳ x = sym (+-suc x x)
--
-- ∃-odd′ ⟨ x , refl ⟩ rewrite sym (+-rearrange x x 0 1)
--           | +-comm (x + x) 1
--           | +-identityʳ x = odd-suc (∃-even′ ⟨ x ,
--               (begin
--                 x + (x + zero)
--               ≡⟨ sym (+-assoc x x 0) ⟩
--                 x + x + 0
--               ≡⟨ +-identityʳ (x + x) ⟩
--                 x + x
--               ∎)
--            ⟩)

-- Exercise ∃-+-≤

∃-+-≤ : ∀ {y z : ℕ}
  → ∃[ x ] (x + y ≡ z)
    ------------------
  → y ≤ z
∃-+-≤ ⟨ zero , refl ⟩ = ≡-implies-≤ refl
∃-+-≤ {y} ⟨ suc x , refl ⟩ = +-monoˡ-≤ 0 (suc x) y _≤_.z≤n

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to = λ ¬∃xy a bx → ¬∃xy ⟨ a , bx ⟩
    ; from = λ ∀¬xy → λ{ ⟨ a , bx ⟩ → ∀¬xy a bx }
    ; from∘to = λ ¬∃xy → extensionality (λ{ ⟨ a , bx ⟩ → refl })
    ; to∘from = λ y → refl
    }

-- Exercise ∃¬-implies-¬∀

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬bx ⟩ = λ x → ¬bx (x a)

-- - ¬∀-implies-∃¬ not stands, because type A might have no legal term

-- Exercise Bin-isomorphism

open Bin
open One
open Can

-- Guarantee: a ≡ b → B a ≡ B b
≡-homomorphism : ∀ {A : Set}
  → (A → Set)
  → Set
≡-homomorphism {A} B =
  ∀ {x : A}
  → (bx : B x)
  → (by : B x)
    ----------
  → bx ≡ by

Σ-≡ : ∀ {A : Set} {B : A → Set} {a c : A}
  → ≡-homomorphism B
  → a ≡ c
  → (b : B a)
  → (d : B c)
    ---------------------
  → ⟨ a , b ⟩ ≡ ⟨ c , d ⟩
Σ-≡ ≡-homo a≡c ba bc rewrite a≡c | ≡-homo ba bc = refl

One-≡-homo : ≡-homomorphism One
One-≡-homo one one = refl
One-≡-homo (suc-one x) (suc-one y) = cong suc-one (One-≡-homo x y)
One-≡-homo (suc-zero x) (suc-zero y) = cong suc-zero (One-≡-homo x y)

Can-≡-homo : ≡-homomorphism Can
Can-≡-homo zero zero = refl
Can-≡-homo zero (from-one (suc-zero ()))
Can-≡-homo (from-one (suc-zero ())) zero
Can-≡-homo (from-one x) (from-one y) = cong from-one (One-≡-homo x y)

-- lemma : ∀ (x : Bin) (y : Can x)
--   → ⟨ to (from x) , to-can {from x} ⟩ ≡ ⟨ x , y ⟩
-- lemma = {!   !}

Bin-isomorphism : ℕ ≃ ∃[ x ](Can x)
Bin-isomorphism =
  record
    { to = λ{ n → ⟨ to n , to-can {n} ⟩ }
    ; from = λ{ ⟨ x , y ⟩ → from x }
    ; from∘to = from-to
    ; to∘from = λ{ ⟨ x , y ⟩ → Σ-≡ Can-≡-homo (to-from x y) (to-can {from x}) y }
    }

-- import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
