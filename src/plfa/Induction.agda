module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Exercise operators

-- associative, commutative, and distribute over one another

data Bool : Set where
  True  : Bool
  False : Bool

_∨_ : Bool → Bool → Bool
n ∨ True = True
n ∨ False = n

-- associative but is not commutative: Matrix Multiply

-- Associativity

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Commutativity

-- lemma 1

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- lemma 2

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- proposition

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Corollary: rearranging

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- Creation

-- Exercise finite-+-assoc

--   Honestly, I have no idea about what should I do lol

-- Associativity rewrite

-- +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- +-assoc′ zero    n p                         = refl
-- +-assoc′ (suc m) n p  rewrite +-assoc′ m n p = refl

-- Commutativity rewrite

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Building proofs interactively

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

-- Exercise +-swap

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    m + n + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    n + m + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

-- Exercise *-distrib-+

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p                                          = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

-- Exercise *-assoc

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

-- Exercise *-comm

*-zero : ∀ (m : ℕ) → m * 0 ≡ 0
*-zero zero = refl
*-zero (suc m) = *-zero m

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero = *-zero m
*-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

-- Exercise 0∸n≡0

∸-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-zero zero = refl
∸-zero (suc n) = refl

-- Exercise ∸-+-assoc

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite ∸-zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

-- Bin-laws

--  I have no idea with duplicate import
--  import plfa.Naturals using (Bin; inc; to; from)

--  Definition

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 m) = x1 m
inc (x1 m) = x0 inc m

to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 1 + 2 * from n

--  Exercise

inc-suc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
inc-suc nil = refl
inc-suc (x0 x) = refl
inc-suc (x1 x) rewrite inc-suc x | +-suc (suc (from x)) (from x + 0) = refl

-- to (from x) ≡ x is false:
--   to ( from (x0 x0 nil)) ≡ x0 nil != x0 x0 nil

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite inc-suc (to n) | from-to n = refl

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
