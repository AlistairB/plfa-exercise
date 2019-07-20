module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

-- Exercise ⇔≃×

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩
    ; from = λ AB×BA → record { to = proj₁ AB×BA ; from = proj₂ AB×BA }
    ; from∘to = λ x → refl
    ; to∘from = λ y → η-× y
    }

data T : Set where

  tt :
    --
    T

η-T : ∀ (w : T) → tt ≡ w
η-T tt = refl

T-count : T → ℕ
T-count tt = 1

T-identifyˡ : ∀ {A : Set} → T × A ≃ A
T-identifyˡ =
  record
    { to = proj₂
    ; from = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ y → refl
    }

T-identifyʳ : ∀ {A : Set} → (A × T) ≃ A
T-identifyʳ {A} =
  ≃-begin
    (A × T)
  ≃⟨ ×-comm ⟩
    (T × A)
  ≃⟨ T-identifyˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -------
  → C
case-⊎ a b (inj₁ x) = a x
case-⊎ a b (inj₂ x) = b x

η-⊎ : ∀ {A B C : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infix 1 _⊎_

-- Exercise ⊎-comm

⊎-comm : ∀ {A B C : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ { (inj₁ a) → (inj₂ a) ; (inj₂ b) → (inj₁ b) }
    ; from = λ { (inj₁ a) → (inj₂ a) ; (inj₂ b) → (inj₁ b) }
    ; from∘to = λ { (inj₁ a) → refl ; (inj₂ b) → refl }
    ; to∘from = λ { (inj₁ a) → refl ; (inj₂ b) → refl }
    }

-- Exercise ⊎-assoc

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ { (inj₁ (inj₁ a)) → inj₁ a
             ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
             ; (inj₂ c) → inj₂ (inj₂ c) }
    ; from = λ { (inj₁ a) → inj₁ (inj₁ a)
               ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
               ; (inj₂ (inj₂ c)) → inj₂ c }
    ; from∘to = λ { (inj₁ (inj₁ a)) → refl
                  ; (inj₁ (inj₂ b)) → refl
                  ; (inj₂ c) → refl }
    ; to∘from = λ { (inj₁ a) → refl
                  ; (inj₂ (inj₁ b)) → refl
                  ; (inj₂ (inj₂ c)) → refl }
    }

data ⊥ : Set where
  -- No statement

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise ⊥-identityˡ

⊥-identityˡ : ∀ {B : Set} → ⊥ ⊎ B ≃ B
⊥-identityˡ =
  record
    { to = λ { (inj₂ b) → b }
    ; from = λ { b → (inj₂ b) }
    ; from∘to = λ { (inj₂ b) → refl }
    ; to∘from = λ { b → refl }
    }

-- Exercise ⊥-identityʳ

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to = λ { (inj₁ a) → a }
    ; from = λ { a → (inj₁ a) }
    ; from∘to = λ { (inj₁ a) → refl }
    ; to∘from = λ { a → refl }
    }

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to = λ f → λ{ ⟨ x , y ⟩ → f x y }
    ; from = λ g x y → g ⟨ x , y ⟩
    ; from∘to = λ x → refl
    ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl } }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    ; from = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ x) → refl}
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ f → extensionality λ x → η-× (f x)
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
            ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
            }
    ; from = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
              ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
              }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl ; ⟨ inj₂ y , z ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl ; (inj₂ ⟨ y , z ⟩) → refl }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
            ; (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
            }
    ; from = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
              ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
              ; ⟨ inj₂ z , _ ⟩ → inj₂ z
              }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl ; (inj₂ z) → refl }
    }

-- Exercise ⊎-weak-×

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

-- Exercise ⊎×-implies-×⊎

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ (inj₁ a) , (inj₁ b) ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ (inj₂ c) , (inj₂ d) ⟩

-- ⊎×-implies-×⊎ don't stands. Consider explanation:
-- A B C D
-- -------
-- 0 1 1 0
