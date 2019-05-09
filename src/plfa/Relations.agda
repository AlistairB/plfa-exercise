module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc; *-comm)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.Induction using (Bin; nil; x0_; x1_; inc; to; from; from-to; +-identityʳ)

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
    One (x1 nil)

  suc-one : ∀ {n : Bin}
    → One n
    ------------
    → One (x1 n)

  suc-zero : ∀ {n : Bin}
    → One n
    ------------
    → One (x0 n)

data Can : Bin → Set where

  zero :
    -----------
    Can (x0 nil)

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

-- It seems like we need a operator +-Bin to prove this.

_+-Bin_ : Bin → Bin → Bin
nil +-Bin b = b
(x0 a) +-Bin nil = (x0 a)
(x0 a) +-Bin (x0 b) = x0 (a +-Bin b)
(x0 a) +-Bin (x1 b) = x1 (a +-Bin b)
(x1 a) +-Bin nil = (x1 a)
(x1 a) +-Bin (x0 b) = x1 (a +-Bin b)
(x1 a) +-Bin (x1 b) = x0 (inc (a +-Bin b))

+-Bin-zeroˡ : ∀ {m : Bin}
  → Can m
    --------------------
  → (x0 nil) +-Bin m ≡ m
+-Bin-zeroˡ zero = refl
+-Bin-zeroˡ (from-one one) = refl
+-Bin-zeroˡ (from-one (suc-one x)) = refl
+-Bin-zeroˡ (from-one (suc-zero x)) = refl

+-Bin-incˡ : ∀ {m n : Bin}
  → (inc m) +-Bin n ≡ inc (m +-Bin n)
+-Bin-incˡ {nil} {nil} = refl
+-Bin-incˡ {nil} {x0 n} = refl
+-Bin-incˡ {nil} {x1 n} = refl
+-Bin-incˡ {x0 m} {nil} = refl
+-Bin-incˡ {x0 m} {x0 n} = refl
+-Bin-incˡ {x0 m} {x1 n} = refl
+-Bin-incˡ {x1 m} {nil} = refl
+-Bin-incˡ {x1 m} {x0 n} rewrite +-Bin-incˡ {m} {n} = refl
+-Bin-incˡ {x1 m} {x1 n} rewrite +-Bin-incˡ {m} {n} = refl

+-Bin-homomorphism : ∀ (a b : ℕ)
  → to (a + b) ≡ (to a) +-Bin (to b)
+-Bin-homomorphism zero b rewrite +-Bin-zeroˡ (to-can {b}) = refl
+-Bin-homomorphism (suc a) b rewrite +-Bin-incˡ {to a} {to b}
                                    | +-Bin-homomorphism a b = refl

+-Bin-double : ∀ (m : Bin)
  → One m
    ----------------
  → m +-Bin m ≡ x0 m
+-Bin-double _ one = refl
+-Bin-double (x1 m) (suc-one onem) rewrite +-Bin-double m onem = refl
+-Bin-double (x0 m) (suc-zero onem) rewrite +-Bin-double m onem = refl

to-from-one : ∀ (x : Bin)
  → One x
    ---------------
  → to (from x) ≡ x

to-from-one _ one = refl
to-from-one (x1 x) (suc-one onex) rewrite +-identityʳ (from x)
                                    | +-Bin-homomorphism (from x) (from x)
                                    | to-from-one x onex
                                    | +-Bin-double x onex = refl
to-from-one (x0 x) (suc-zero onex) rewrite +-identityʳ (from x)
                                    | +-Bin-homomorphism (from x) (from x)
                                    | to-from-one x onex
                                    | +-Bin-double x onex = refl

to-from : ∀ (x : Bin)
  → Can x
    ---------------
  → to (from x) ≡ x

to-from _ zero = refl
to-from x (from-one onex) = to-from-one x onex
