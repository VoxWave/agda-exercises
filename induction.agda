import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
  -- begin
  --   (zero + n) + p
  -- ≡⟨⟩
  --   n + p
  -- ≡⟨⟩
  --   zero + (n + p)
  -- ∎
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
  ≡⟨ cong suc (+-identityʳ m)⟩
    suc m
  ∎

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
    suc ( m + suc n )
  ≡⟨ cong suc (+-suc m n)⟩
    suc ( suc ( m + n ) )
  ≡⟨⟩
    suc( (suc m) + n )
  ∎

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
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
  ≡⟨⟩
    m + (n + p) + q
  ∎

+-assoc´ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc´ zero n p = refl
+-assoc´ (suc m) n p rewrite +-assoc´ m n p = refl

+-identity´ : ∀ (n : ℕ) → n + zero ≡ n
+-identity´ zero = refl
+-identity´ (suc n) rewrite +-identity´ n = refl

+-suc´ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc´ zero n = refl
+-suc´ (suc m) n rewrite +-suc´ m n = refl

+-comm´ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm´ m zero rewrite +-identity´ m = refl
+-comm´ m (suc n) rewrite +-suc´ m n | +-comm´ m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-suc´ n (m + p) | +-swap m n p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc´ p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-identityʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-identityʳ zero = refl
*-identityʳ (suc m) rewrite *-identityʳ m = refl

*-identity : ∀ (m : ℕ) → m ≡ m * 1
*-identity zero = refl
*-identity (suc m) rewrite sym (*-identity m) = refl

*-suc : ∀ (m n : ℕ) → n * suc m ≡ n + n * m
*-suc m zero = refl
*-suc m (suc n) rewrite sym (+-assoc n m (n * m)) | +-comm n m | *-suc m n | +-assoc m n (n * m) = refl

*-distrib-+' : ∀ (m n p : ℕ) → p * (m + n) ≡ p * m + p * n
*-distrib-+' zero n p rewrite *-identityʳ p | +-comm´ 0 p = refl
*-distrib-+' (suc m) n p rewrite *-suc m p | *-suc (m + n) p | *-distrib-+' m n p | +-assoc p (p * m) (p * n) = refl

+-sucisplusone : ∀ (x : ℕ) → suc x ≡ x + 1
+-sucisplusone zero rewrite +-identity´ 1 = refl
+-sucisplusone (suc x) rewrite +-sucisplusone x = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-identityʳ n = refl
*-comm (suc m) n rewrite *-comm m n | +-sucisplusone m | *-distrib-+' m 1 n | sym (*-identity n) | +-comm n (n * m) = refl

0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

-- ∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
-- ∸-|-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
-- ∸-|-assoc (suc m) zero p = refl
-- ∸-|-assoc (suc m) (suc n) zero rewrite +-identity´ n = refl
-- ∸-|-assoc (suc m) (suc n) (suc p) rewrite +-sucisplusone p | sym (+-assoc n p 1) | sym (∸-|-assoc m (n + p) 1) | sym (∸-|-assoc m n p) | ∸-|-assoc m n (p + 1) | sym (+-assoc n p 1) | sym (∸-|-assoc m (n + p) 1) | sym (∸-|-assoc m n p) = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p rewrite ∸-|-assoc m n p = refl
