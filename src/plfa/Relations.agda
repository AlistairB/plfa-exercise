module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc; *-comm)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.Induction using (Bin; nil; x0_; x1_; inc; to; from; from-to)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      -------------
    →   zero ≤ n

  s≤s : ∀ {m n : ℕ}
    →     m ≤ n
      -------------
    → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_

-- Exercise orderings

--  a preorder that is not a partial order: ⊂ of every Set
--  a partial order that is not a total order: (Z*, |)

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl -- s≤s (≤-refl {n})

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
   -------
  → m ≤ p
≤-trans z≤n        _        = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

--  Because there's no such n : ℕ let n ≤ 0 unless n ≡ 0

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n    = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m + p ≤ m + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise *-mono-≤

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- Exercise <-trans

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- Exercise trichotomy

data Tri (m n : ℕ) : Set  where

  forward :
      m < n
      -------
    → Tri m n

  flipped :
      n < m
      -------
    → Tri m n

  fixed :
      m ≡ n
      -------
    → Tri m n

<-trichotomy : ∀ (m n : ℕ) → Tri m n
<-trichotomy zero zero = fixed refl
<-trichotomy zero (suc n) = forward z<s
<-trichotomy (suc m) zero = flipped z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | forward m<n = forward (s<s m<n)
...                             | flipped n<m = flipped (s<s n<m)
...                             | fixed   m≡n = fixed (cong suc m≡n)

-- Exercise +-mono-<

+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    ------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Exercise ≤-iff-<

≤-iff-< : ∀ {m n : ℕ}
  → suc m ≤ n
    ---------
  → m < n
≤-iff-< {zero} (s≤s m≤n) = z<s
≤-iff-< {suc m} (s≤s m≤n) = s<s (≤-iff-< m≤n)

<-iff-≤ : ∀ {m n : ℕ}
  → m < n
    ---------
  → suc m ≤ n
<-iff-≤ z<s = s≤s z≤n
<-iff-≤ (s<s m<n) = s≤s (<-iff-≤ m<n)

-- Exercise <-trans-revisited

<-cond-≤ : ∀ {m n : ℕ}
  → m < n
    -----
  → m ≤ n
<-cond-≤ z<s = z≤n
<-cond-≤ (s<s m<n) = s≤s (<-cond-≤ m<n)

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans-revisited m<n n<p = ≤-iff-< (≤-trans (s≤s (<-cond-≤ m<n)) (<-iff-≤ n<p))


data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd  m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

-- Exercise o+o≡e

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)

e+o≡o zero on = on
e+o≡o (suc x) on = suc (o+o≡e x on)

o+o≡e (suc x) n = suc (e+o≡o x n)

-- Exercise Bin-predicates

--  Predicates

data One : Bin → Set where

  one :
    -------------
    One (x1_ nil)

  suc-one : ∀ {n : Bin}
    → One n
    ------------
    → One (x1_ n)

  suc-zero : ∀ {n : Bin}
    → One n
    ------------
    → One (x0_ n)

data Can : Bin → Set where

  zero :
    -----------
    Can (x0_ nil)

  from-one : ∀ {n : Bin}
    → One n
      -----
    → Can n

--  Prove

inc-keeps-one : ∀ {x : Bin}
  → One x
    -----------
  → One (inc x)

inc-keeps-one one = suc-zero one
inc-keeps-one (suc-one onex) = suc-zero (inc-keeps-one onex)
inc-keeps-one (suc-zero onex) = suc-one onex

inc-keeps : ∀ {x : Bin}
  → Can x
    -----------
  → Can (inc x)

inc-keeps zero = from-one one
inc-keeps (from-one onex) = from-one (inc-keeps-one onex)

to-can : ∀ {n : ℕ}
    ----------
  → Can (to n)

to-can {zero} = zero
to-can {suc n} = inc-keeps (to-can {n})

--  - to-from

to-double : ∀ {x : Bin}
  → One x
    ---------------------------
  → to (2 * from x) ≡ x0 x

to-double one = refl
to-double (suc-one onex) = {!   !}
to-double (suc-zero onex) = {!   !}

-- It seems like we need a operator +-Bin to prove this lemma.

to-from-one : ∀ {x : Bin}
  → One x
    ---------------
  → to (from x) ≡ x

to-from-one one = refl
to-from-one (suc-one onex) = {!   !}
to-from-one (suc-zero onex) = {!   !}

to-from : ∀ {x : Bin}
  → Can x
    ---------------
  → to (from x) ≡ x

to-from zero = refl
to-from (from-one onex) = to-from-one onex
