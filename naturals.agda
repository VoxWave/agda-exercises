import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module naturals where
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc_ : Bin → Bin
inc nil = x1 nil
inc x0 rest = x1 rest
inc x1 rest = x0 inc rest

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

_ : inc (x0 nil) ≡ x1 nil
_ = refl

_ : inc (x1 nil) ≡ x0 x1 nil
_ = refl

_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ = refl

_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ = refl

_ : inc (x0 x0 x1 nil) ≡ x1 x0 x1 nil
_ = refl

to_ : ℕ → Bin
to zero = x0 nil
to suc n = inc (to n)

fromtrue : Bin → ℕ → ℕ
fromtrue (nil) _ = 0
fromtrue (x0 rest) n = fromtrue rest (n + 1)
fromtrue (x1 rest) n = (2 ^ n) + fromtrue rest (n + 1)

from_ : Bin → ℕ
from n = fromtrue n 0

_ : to 0 ≡ x0 nil
_ = refl

_ : to 1 ≡ x1 nil
_ = refl

_ : to 2 ≡ x0 x1 nil
_ = refl

_ : to 3 ≡ x1 x1 nil
_ = refl

_ : to 4 ≡ x0 x0 x1 nil
_ = refl 

_ : to 7 ≡ x1 x1 x1 nil
_ = refl

_ : from (x0 nil) ≡ 0
_ = refl

_ : from (x1 nil) ≡ 1
_ = refl

_ : from (x0 x1 nil) ≡ 2
_ = refl

_ : from (x1 x1 nil) ≡ 3
_ = refl

_ : from (x0 x0 x1 nil) ≡ 4
_ = refl

_ : from (x1 x1 x1 nil) ≡ 7
_ = refl

_ : from (to 7) ≡ 7
_ = refl

_ : to (from (x1 x1 x1 nil)) ≡ x1 x1 x1 nil
_ = refl

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

_ : seven ≡ 7
_ = refl

_ : 2 + 70 ≡ 72
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (suc (suc zero)) + suc( suc( suc( suc zero)))
  ≡⟨⟩
    suc (suc (suc zero) + suc( suc( suc (suc zero))))
  ≡⟨⟩
    suc (suc (suc zero + suc( suc( suc ( suc zero)))))
  ≡⟨⟩
    suc( suc( suc(zero + suc( suc( suc( suc zero))))))
  ≡⟨⟩
    suc( suc (suc ( suc( suc( suc( suc zero))))))
  ≡⟨⟩
    7
  ∎

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc(2 + 4)
  ≡⟨⟩
    suc(suc(1 + 4))
  ≡⟨⟩
    suc(suc(suc zero + 4))
  ≡⟨⟩
    suc(suc(suc(4)))
  ≡⟨⟩
    suc(suc(5))
  ≡⟨⟩
    suc(6)
  ≡⟨⟩
    7
  ∎

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + ( 2 * 4 )
  ≡⟨⟩
    4 + ( 4 + (1 * 4) )
  ≡⟨⟩
    4 + (4 + ( 4 + (0 * 4) ))
  ≡⟨⟩
    4 + ( 4 + ( 4 + 0))
  ≡⟨⟩
    12
  ∎

_ : 3 ^ 4 ≡ 81
_ = refl

_ : 2 ^ 8 ≡ 256
_ = refl

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
