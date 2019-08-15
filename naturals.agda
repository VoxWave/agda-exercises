import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module naturals where
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- I edited this file
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

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
