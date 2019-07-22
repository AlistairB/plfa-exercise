module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import plfa.Isomorphism using (_≃_; extensionality; _⇔_)
open import plfa.Relations using (_<_)
open import Function using (_∘_)
open import plfa.Connectives using (→-distrib-⊎)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition p ¬b = λ x → ¬b (p x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Exercise <-irreflexive

open _<_

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s x) = <-irreflexive x

-- Exercise trichotomy

suc-≡ : ∀ {m n : ℕ}
  → suc m ≡ suc n
    -------------
  → m ≡ n
suc-≡ suc≡ = cong (λ x → x ∸ 1) suc≡

data Tri (m n : ℕ) : Set  where

  forward :
      (m < n) × ¬ (m ≡ n) × ¬ (n < m)
      -------
    → Tri m n

  fixed :
      ¬ (m < n) × (m ≡ n) × ¬ (n < m)
      -------
    → Tri m n

  flipped :
      ¬ (m < n) × ¬ (m ≡ n) × (n < m)
      -------
    → Tri m n

trichotomy : ∀ (m n : ℕ) → Tri m n

-- I have to say _,_ is way more clear
trichotomy zero zero = fixed ((λ ()) , refl , (λ ()))
trichotomy zero (suc n) = forward (z<s , (λ ()) , (λ ()))
trichotomy (suc m) zero = flipped ((λ ()) , (λ ()) , z<s)
trichotomy (suc m) (suc n) with trichotomy m n
... | forward (m<n , ¬m≡n , ¬n<m) = forward (s<s m<n , (λ x → ¬m≡n (suc-≡ x)) , λ{ (s<s n<m) → ¬n<m n<m })
... | flipped (¬m<n , ¬m≡n , n<m) = flipped ((λ{ (s<s m<n) → ¬m<n m<n }) , (λ x → ¬m≡n (suc-≡ x)) , s<s n<m)
... | fixed (¬m<n , m≡n , ¬n<m) = fixed ((λ{ (s<s m<n) → ¬m<n m<n }) , cong suc m≡n  , λ{ (s<s n<m) → ¬n<m n<m })

-- Exercise ⊎-dual-×

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

¬⊎-implies-¬× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
¬⊎-implies-¬× = λ{ (inj₁ ¬a) → λ x → ¬a (proj₁ x) ; (inj₂ ¬b) → λ x → ¬b (proj₂ x) }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ z → z (inj₂ (λ x → z (inj₁ x)))

-- Exercise Classical

em-implies-¬¬-elim :
    (∀ {A : Set} → (A ⊎ ¬ A))
    -------------------------
  → ∀ {A′ : Set} → (¬ ¬ A′ → A′)
em-implies-¬¬-elim lem {A′} with lem {A′}
... | inj₁ a = λ x → a
... | inj₂ ¬a = λ x → ⊥-elim (x ¬a)

¬¬-elim-implies-pierce :
    (∀ {A : Set} → (¬ ¬ A → A))
    -------------------------------------
  → ∀ {A′ B : Set} → ((A′ → B) → A′) → A′
¬¬-elim-implies-pierce elim {A′} = λ x → elim {A′} λ ¬a → (contraposition x) ¬a λ a → ⊥-elim (¬a a)

¬¬-elim-implies-pierce′ :
    (∀ {A : Set} → (¬ ¬ A → A))
    -------------------------------------
  → ∀ {A′ B : Set} → ((A′ → B) → A′) → A′
-- Proof by Auto
¬¬-elim-implies-pierce′ elim {A′} = λ x → elim {A′} λ ¬a → ¬a (x λ a → elim (λ _ → ¬a a)) -- ???

pierce-implies-→⊎ :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → ∀ {A′ B′ : Set} → (A′ → B′) → ¬ A′ ⊎ B′
pierce-implies-→⊎ pierce = λ a→b → pierce λ x → inj₁ λ a → x (inj₂ (a→b a))

-- →⊎-de-morgan seems hard to prove

t-id : ∀ {A : Set} → A → A
t-id x = x

→⊎-implies-em :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → ∀ {A′ : Set} → (A′ ⊎ ¬ A′)
→⊎-implies-em →⊎ {A′} with →⊎ {A′} t-id
... | inj₁ ¬a = inj₂ ¬a
... | inj₂ a = inj₁ a

-- Proof loop end

¬¬-elim-implies-de-morgan :
    (∀ {A : Set} → (¬ ¬ A → A))
    ----------------------------------------
  → ∀ {A′ B : Set} → ¬ (¬ A′ × ¬ B) → A′ ⊎ B
¬¬-elim-implies-de-morgan elim = λ z → elim λ x → z ((λ a → x (inj₁ a)) , λ b → x (inj₂ b))

de-morgan-implies-em :
    (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
    ---------------------------------------
  → ∀ {A′ : Set} → (A′ ⊎ ¬ A′)
de-morgan-implies-em demorgan = demorgan λ x → proj₂ x (proj₁ x)

-- Exercise Stable

Stable : Set → Set
Stable A = ¬ ¬ A → A

neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable = λ ¬¬¬a a → (¬¬¬-elim ¬¬¬a) a

×-stable : ∀ {A B : Set}
  → Stable A
  → Stable B
    --------------
  → Stable (A × B)
×-stable sa sb = λ ¬¬ab → sa (λ ¬a → ¬¬ab λ ab → ¬a (proj₁ ab)) ,
  sb λ ¬b → ¬¬ab λ ab → ¬b (proj₂ ab)
