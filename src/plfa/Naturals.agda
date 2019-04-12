module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n  = n           -- 0 + n       ≡ n
suc m + n = suc (m + n) -- (1 + m) + n ≡ 1 + (m + n)

_ : 1 + 1 ≡ 2
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc 2 + 4
  ≡⟨⟩
    suc (suc 1 + 4)
  ≡⟨⟩
    suc (suc (suc 0 + 4))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ 0     = 1
n ^ suc m = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero      = m
zero ∸ suc n  = zero
suc m ∸ suc n = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 m) = x1 m
inc (x1 m) = x0 inc m

_ : inc (x0 nil) ≡ x1 nil
_ = refl

_ : inc (x1 nil) ≡ x0 x1 nil
_ = refl

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

to : ℕ → Bin
to zero = nil
to (suc n) = inc (to n)

_ : to 3 ≡ x1 x1 nil
_ = refl

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 1 + 2 * from n

_ : from (x0 x0 x1 x1 nil) ≡ 12
_ = refl

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
