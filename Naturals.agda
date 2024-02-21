module Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (1 + 2))
  ≡⟨⟩
    suc (suc (suc (0 + 2)))
  ≡⟨⟩
    suc (suc (suc 2))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

-- Practice exercise
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (2 + 3))
  ≡⟨⟩  -- ^ Our earlier proof
    suc (suc 5)
  ≡⟨⟩
    7
  ∎


-- Multiplication
_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
m ^ 0       = 1
m ^ (suc n) = m * (m ^ n)


_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero      = m
zero ∸ suc n  = zero
suc m ∸ suc n = m ∸ n

_ : 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_


_+'_ : ℕ → ℕ → ℕ
zero +' n  = n
suc m +' n = suc (m +' n)


{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

b11 : Bin
b11 = ⟨⟩ I O I I

{-

  `dec` is a bit strange; I think part of the issue is the representation.
  Could investigate a bit more 

dec : Bin → Bin
dec ⟨⟩     = ⟨⟩
dec (⟨⟩ O) = ⟨⟩
dec (b I)  = b O
dec (b O)  = dec b I

-- dec (⟨⟩ O)    = ⟨⟩ O
-- dec (b I)     = b O
-- dec ((b O) O) = dec b O I
-- dec ((b I) O) = b O I

dec-ex : dec (⟨⟩ I I O O) ≡ ⟨⟩ I O I I
dec-ex = refl

dec-1 : dec (⟨⟩ I) ≡ ⟨⟩
dec-1 = refl

dec-2 : dec (⟨⟩ I O) ≡ ⟨⟩ I
dec-2 = refl
  -- begin
  --   dec (⟨⟩ I O)
  -- ≡⟨⟩
  --   dec (⟨⟩ I) I
  -- ≡⟨⟩
  --   (⟨⟩ O) I
  -- ≡⟨⟩
  --   ⟨⟩ O I
  -- ∎

dec-3 : dec (⟨⟩ I I) ≡ ⟨⟩ I O
dec-3 = refl

dec-4 : dec (⟨⟩ I O O) ≡ ⟨⟩ I I
dec-4 = refl

dec-5 : dec (⟨⟩ I O I) ≡ ⟨⟩ I O O
dec-5 = refl
-}

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (x O) = x I
inc (x I) = inc x O

inc-ex : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
inc-ex = refl

inc-0 : inc (⟨⟩ O) ≡ ⟨⟩ I
inc-0 = refl

inc-1 : inc (⟨⟩ I) ≡ ⟨⟩ I O
inc-1 = refl

inc-2 : inc (⟨⟩ I O) ≡ ⟨⟩ I I
inc-2 = refl

inc-3 : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
inc-3 = refl

inc-4 : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
inc-4 = refl

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc x) = inc (to x)

to-0 : to 0 ≡ ⟨⟩ O
to-0 = refl

to-1 : to 1 ≡ ⟨⟩ I
to-1 = refl

to-2 : to 2 ≡ ⟨⟩ I O
to-2 = refl

to-3 : to 3 ≡ ⟨⟩ I I
to-3 = refl

to-4 : to 4 ≡ ⟨⟩ I O O
to-4 = refl

to-255 : to 255 ≡ (⟨⟩ I I I I I I I I)
to-255 = refl


len : Bin → ℕ
len ⟨⟩ = 0
len (x O) = len x + 1
len (x I) = len x + 1


from : Bin → ℕ
from ⟨⟩    = 0
from (b O) = 2 * from b
from (b I) = 1 + 2 * from b

from-0 : from ⟨⟩ ≡ 0
from-0 = refl

from-1 : from (⟨⟩ I) ≡ 1
from-1 = refl

from-2 : from (⟨⟩ I O) ≡ 2
from-2 = refl

from-3 : from (⟨⟩ I I) ≡ 3
from-3 = refl

_ : from (⟨⟩ I I I I I I I I) ≡ 255
_ = refl
