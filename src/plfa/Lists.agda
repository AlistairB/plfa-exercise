module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_; extensionality)
open import plfa.Induction using (*-distrib-+; ∸-+-assoc; *-comm; +-comm)
open import plfa.Quantifiers using (∀-extensionality)
open import Data.Empty using (⊥; ⊥-elim)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

-- {-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (_∷_ x) (++-identityʳ xs)

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

-- Exercise reverse-involutive

reverse-extract : ∀ {A : Set} (xs : List A) (x : A)
  → reverse (xs ++ [ x ]) ≡ x ∷ reverse xs
reverse-extract [] _ = refl
reverse-extract (x ∷ xs) y = cong (_++ [ x ]) (reverse-extract xs y)

reverse-involutive : ∀ {A : Set} {xs : List A}
  → reverse (reverse xs) ≡ xs
reverse-involutive {A} {[]} = refl
reverse-involutive {A} {x ∷ xs} =
  begin
      reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-extract (reverse xs) x ⟩
      (x ∷ reverse (reverse xs))
  ≡⟨ cong (x ∷_) (reverse-involutive {A} {xs}) ⟩
      (x ∷ xs)
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys rewrite shunt-reverse xs (x ∷ ys) = sym (++-assoc (reverse xs) [ x ] ys)

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs rewrite shunt-reverse xs [] = ++-identityʳ (reverse xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

sucs : List ℕ → List ℕ
sucs = map suc

-- Exercise map-compose

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} {B} {C} {f} {g} = extensionality (lemma f g)
  where
    lemma : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
      → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    lemma _ _ [] = refl
    lemma f g (x ∷ xs) = cong ((g ∘ f) x ∷_) (lemma f g xs)

-- Exercise map-++-commute

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute {A} {B} {f} {[]} {ys} = refl
map-++-commute {A} {B} {f} {x ∷ xs} {ys} = cong (f x ∷_) (map-++-commute {A} {B} {f} {xs} {ys})

-- Exercise map-Tree

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set}
  → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node lf x rt) = node (map-Tree f g lf) (g x) (map-Tree f g rt)

--

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

-- Exercise product

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

-- Exercise foldr-++

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

-- Exercise map-is-foldr

map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {B} {f} = extensionality lemma
  where
    lemma : ∀ {A B : Set} {f : A → B} (xs : List A) →
      map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    lemma [] = refl
    lemma {A} {B} {f} (x ∷ xs) = cong (f x ∷_) (lemma xs)

-- Exercise fold-Tree

fold-Tree : ∀ {A B C : Set}
  → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node lf x rt) = g (fold-Tree f g lf) x (fold-Tree f g rt)

-- Exercise map-is-fold-Tree

map-is-fold-Tree : ∀ {A B C D : Set} {f : A → C} {g : B → D} →
  map-Tree f g ≡ fold-Tree {A} {B} {Tree C D} (λ x → leaf (f x)) (λ lf x rt → node lf (g x) rt)
map-is-fold-Tree = extensionality lemma
  where
    lemma : ∀ {A B C D : Set} {f : A → C} {g : B → D} (xs : Tree A B) →
      map-Tree f g xs ≡ fold-Tree {A} {B} {Tree C D} (λ x → leaf (f x)) (λ lf x rt → node lf (g x) rt) xs
    lemma (leaf x) = refl
    lemma {A} {B} {C} {D} {f} {g} (node lf x rt) rewrite lemma {A} {B} {C} {D} {f} {g} lf | lemma {A} {B} {C} {D} {f} {g} rt = refl

-- Exercise sum-downFrom

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

-- - Okay, I f**ked it up

{-

suc-∸ : ∀ (m n : ℕ) → suc (m ∸ n) ≡ suc m ∸ n
suc-∸ m n = {!   !}

+-∸-assoc : ∀ (m n p : ℕ)
  → m + (n ∸ p) ≡ m + n ∸ p
+-∸-assoc zero n p = refl
+-∸-assoc (suc m) n p rewrite +-∸-assoc m n p = suc-∸ (m + n) p

+-∸-comm : ∀ (m n p : ℕ)
  → m ∸ n + p ≡ m + p ∸ n
+-∸-comm m zero p = refl
+-∸-comm zero (suc n) p = {!   !}
+-∸-comm (suc m) (suc n) p = {!   !}

∸-elim : ∀ (m n : ℕ)
  → m ≡ n
    -----
  → m ∸ n ≡ 0
∸-elim m n m≡n = {!   !}

*-distrib-∸ : ∀ (p m n : ℕ)
  → p * (m ∸ n) ≡ p * m ∸ p * n
*-distrib-∸ zero m n = refl
*-distrib-∸ (suc p) m n =
  begin
    m ∸ n + p * (m ∸ n)
  ≡⟨ cong (m ∸ n +_) (*-distrib-∸ p m n) ⟩
    m ∸ n + (p * m ∸ p * n)
  ≡⟨ +-∸-assoc (m ∸ n) (p * m) (p * n) ⟩
    m ∸ n + p * m ∸ p * n
  ≡⟨ cong (_∸ p * n) (+-∸-comm m n (p * m)) ⟩
    (m + p * m) ∸ n ∸ p * n
  ≡⟨ sym (lemma m (p * m) n (p * n)) ⟩
    m + (p * m ∸ n ∸ p * n)
  ≡⟨ cong (m +_) (∸-+-assoc (p * m) n (p * n)) ⟩
    m + (p * m ∸ (n + p * n))
  ≡⟨ +-∸-assoc m (p * m) (n + p * n) ⟩
    m + p * m ∸ (n + p * n)
  ∎
  where
    lemma : ∀ (m n p q : ℕ) → m + (n ∸ p ∸ q) ≡ m + n ∸ p ∸ q
    lemma m n p q rewrite +-∸-assoc m (n ∸ p) q | +-∸-assoc m n p = refl

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
      sum (n ∷ downFrom n) * 2
  ≡⟨⟩
      (n + foldr _+_ 0 (downFrom n)) * 2
  ≡⟨ *-distrib-+ n (foldr _+_ 0 (downFrom n)) 2 ⟩
      n * 2 + foldr _+_ 0 (downFrom n) * 2
  ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
      n * 2 + n * (n ∸ 1)
  ≡⟨ cong (n * 2 +_) (*-distrib-∸ n n 1) ⟩
      n * 2 + (n * n ∸ n * 1)
  ≡⟨ +-∸-assoc (n * 2) (n * n) (n * 1) ⟩
      n * 2 + n * n ∸ n * 1
  ≡⟨ sym (+-∸-comm (n * 2) (n * 1) (n * n)) ⟩
      n * 2 ∸ n * 1 + n * n
  ≡⟨ cong (_+ n * n) (lemma n) ⟩
      n + n * n
  ∎
  where
    lemma : ∀ (n : ℕ) → n * 2 ∸ n * 1 ≡ n
    lemma n rewrite *-comm n 2 | *-comm n 1
      | sym (+-∸-assoc n (n + 0) (n + 0))
      | ∸-elim (n + 0) (n + 0) refl | +-identityʳ n = refl

-}

--

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

-- Exercise foldl

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

-- Exercise foldr-monoid-foldl

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs
foldl-monoid _⊗_ e ⊗-monoid [] y = identityʳ ⊗-monoid y
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
    rewrite identityˡ ⊗-monoid x
          | sym (foldl-monoid _⊗_ e ⊗-monoid xs x)
          | sym (assoc ⊗-monoid y x (foldl _⊗_ e xs))
           = foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x)

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
    -------------------------
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (lemma _⊗_ e ⊗-monoid)
  where
    lemma : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
      → IsMonoid _⊗_ e
        -------------------------------------------------
      → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    lemma _⊗_ e ⊗-monoid [] = refl
    lemma _⊗_ e ⊗-monoid (x ∷ xs)
        rewrite lemma _⊗_ e ⊗-monoid xs
              | foldl-monoid _⊗_ e ⊗-monoid xs x
              | identityˡ ⊗-monoid x = refl

--

data All {A : Set} (P : A → Set) : List A → Set where
    []  : All P []
    _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- Exercise Any-++-⇔

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where

    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys anyp = inj₂ anyp
    to (x ∷ xs) ys (here px) = inj₁ (here px)
    to (x ∷ xs) ys (there anyp) with to xs ys anyp
    ... | inj₁ anyx = inj₁ (there anyx)
    ... | inj₂ anyy = inj₂ anyy

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from _ _ (inj₁ (here ax)) = here ax
    from (x ∷ xs) ys (inj₁ (there ax)) = there (from xs ys (inj₁ ax))
    from [] ys (inj₂ y) = y
    from (x ∷ xs) ys (inj₂ y) = there (from xs ys (inj₂ y))

-- Exercise All-++-≃

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (x : All P (xs ++ ys))
    → from xs ys (to xs ys x) ≡ x
  from∘to [] ys x = refl
  from∘to (x ∷ xs) ys (px ∷ allp) = cong (px ∷_) (from∘to xs ys allp)

  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (y : All P xs × All P ys)
    → to xs ys (from xs ys y) ≡ y
  to∘from [] ys ⟨ [] , snd ⟩ = refl
  to∘from (x ∷ xs) ys ⟨ px ∷ fst , snd ⟩ rewrite to∘from xs ys ⟨ fst , snd ⟩ = refl

-- Exercise ¬Any≃All¬

_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)

¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ P xs =
  record
    { to = to P xs
    ; from = from P xs
    ; from∘to = from∘to P xs
    ; to∘from = to∘from P xs
    }

  where

    to : ∀ {A : Set} (P : A → Set) (xs : List A)
      → (¬_ ∘′ Any P) xs → All (¬_ ∘′ P) xs
    to _ [] _ = []
    to P (x ∷ xs) ¬Any = (λ Px → ¬Any (here Px)) ∷ to P xs λ anyx → ¬Any (there anyx)

    from : ∀ {A : Set} (P : A → Set) (xs : List A)
      → All (¬_ ∘′ P) xs → (¬_ ∘′ Any P) xs
    from P [] [] ()
    from P (x ∷ xs) (¬Px ∷ All¬) (here Px) = ¬Px Px
    from P (x ∷ xs) (¬Px ∷ All¬) (there anyp) = from P xs All¬ anyp

    from∘to : ∀ {A : Set} (P : A → Set) (xs : List A) (x : (¬_ ∘′ Any P) xs)
      → from P xs (to P xs x) ≡ x
    from∘to P [] ¬Any = extensionality λ ()
    from∘to P (x ∷ xs) ¬Any = extensionality
      λ{ (here Px) → refl
       ; (there anyp) → ⊥-elim (¬Any (there anyp))
       }

    to∘from : ∀ {A : Set} (P : A → Set) (xs : List A) (y : All (¬_ ∘′ P) xs)
      → to P xs (from P xs y) ≡ y
    to∘from P [] [] = refl
    to∘from P (x ∷ xs) (¬Px ∷ All¬) = cong (¬Px ∷_) (to∘from P xs All¬)

-- - Proof of negation is too weak to prove ¬All-implies-Any¬

Any¬-implies-¬All : ∀ {A : Set} (P : A → Set) (xs : List A)
  → Any (¬_ ∘′ P) xs → (¬_ ∘′ All P) xs
Any¬-implies-¬All P (x ∷ xs) (here ¬Px) (Px ∷ allp) = ¬Px Px
Any¬-implies-¬All P (x ∷ xs) (there Any¬) (Px ∷ allp) = Any¬-implies-¬All P xs Any¬ allp

--

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

-- Exercise any?

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no λ ()
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | yes Px | _       = yes (here Px)
...                 | _      | yes Pxs = yes (there Pxs)
...                 | no ¬Px | no ¬Pxs = no (λ { (here Px) → ¬Px Px ; (there anyp) → ¬Pxs anyp})

-- Exercise All-∀

-- All-∀ : ∀ {A : Set} (P : A → Set) (xs : List A)
--   → All P xs ≃ (∀ {x} → x ∈ xs → P x)
-- All-∀ {A} P xs =
--   record
--     { to = to xs
--     ; from = from xs
--     ; from∘to = from∘to xs
--     ; to∘from = {! to∘from xs  !} -- wtf ???
--     }
--
--   where
--
--     to : ∀ (xs : List A)
--       → All P xs → (∀ {x} → x ∈ xs → P x)
--     to (x ∷ xs) (Px ∷ allp) (here x≡x′) rewrite x≡x′ = Px
--     to (x ∷ xs) (Px ∷ allp) (there x′∈xs) = to xs allp x′∈xs
--
--     from : ∀ (xs : List A)
--       → (∀ {x} → x ∈ xs → P x) → All P xs
--     from [] ∀x = []
--     from (x ∷ xs) ∀x = ∀x (here refl) ∷ from xs (λ x′∈xs → ∀x (there x′∈xs))
--
--     from∘to : ∀ (xs : List A)
--       → (x : All P xs) → from xs (to xs x) ≡ x
--     from∘to [] [] = refl
--     from∘to (x ∷ xs) (Px ∷ allp) = cong (Px ∷_) (from∘to xs allp)
--
--     to∘from : ∀ (xs : List A)
--       → (y : ∀ {x} → x ∈ xs → P x) → to xs (from xs y) ≡ y
--     to∘from [] ∀y = ∀-extensionality λ ()
--     to∘from (x ∷ xs) ∀y = ∀-extensionality (λ{ (here x) → {!   !} ; (there x′∈xs) → {!   !}})

-- Exercise Any-∃

Any-∃ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ {A} P xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }

  where

    to : ∀ (xs : List A)
      → Any P xs → ∃[ x ] (x ∈ xs × P x)
    to (x ∷ xs) (here Px) = ⟨ x , ⟨ (here refl) , Px ⟩ ⟩
    to (x ∷ xs) (there anyp) with to xs anyp
    ... | ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩ = ⟨ x′ , ⟨ (there x′∈xs) , Px′ ⟩ ⟩

    from : ∀ (xs : List A)
      → ∃[ x ] (x ∈ xs × P x) → Any P xs
    from (x ∷ xs) ⟨ x′ , ⟨ here x′≡x , Px′ ⟩ ⟩ rewrite sym x′≡x = here Px′
    from (x ∷ xs) ⟨ x′ , ⟨ there x′∈xs , Px′ ⟩ ⟩ = there (from xs ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩)

    from∘to : ∀ (xs : List A) (x : Any P xs) → from xs (to xs x) ≡ x
    from∘to (x ∷ xs) (here Px) = refl
    from∘to (x ∷ xs) (there anyp) = cong there (from∘to xs anyp)

    to∘from : ∀ (xs : List A) (y : ∃[ x ] (x ∈ xs × P x)) → to xs (from xs y) ≡ y
    to∘from (x ∷ xs) ⟨ .x , ⟨ here refl , Px′ ⟩ ⟩ = refl
    to∘from (x ∷ xs) ⟨ x′ , ⟨ there x′∈xs , Px′ ⟩ ⟩ =
      cong (λ{ ⟨ x″ , ⟨ x″∈xs , Px″ ⟩ ⟩ → ⟨ x″ , ⟨ (there x″∈xs) , Px″ ⟩ ⟩})
        (to∘from xs ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩)

-- Exercise filter?

filter? : ∀ {A : Set} {P : A → Set}
  → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
filter? P? [] = ⟨ [] , [] ⟩
filter? P? (x ∷ xs) with P? x   | filter? P? xs
...                    | yes Px | ⟨ ys , allys ⟩ = ⟨ x ∷ ys , Px ∷ allys ⟩
...                    | no  _  | ∃ys            = ∃ys

-- - for test

not? : (x : Bool) → Dec (x ≡ false)
not? false = yes refl
not? true = no λ ()

_ : filter? not? [ true , false , true , true , false ]
  ≡ ⟨ [ false , false ] , refl ∷ refl ∷ [] ⟩
_ = refl
