import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _⊕_)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)


id-l : ∀ n → n ≡ n ⊕ zero
id-l zero = refl
id-l (suc n) = cong suc (id-l n)

+-comm : ∀ m n → m ⊕ n ≡ n ⊕ m
+-comm zero n = id-l n
+-comm (suc m) n = lem m n
  where
    lem : ∀ m n → suc m ⊕ n ≡ n ⊕ suc m
    lem m zero = cong suc (sym (id-l m))
    lem m (suc n) = let IH = lem m n in
                    trans (cong suc (let p = lem n m in trans (sym p) (cong suc (+-comm n m)))) (cong suc IH)



data ℤ : Set where
  _,_ : ℕ → ℕ → ℤ

_+_ : ℤ → ℤ → ℤ
(m , m') + (n , n') = (m ⊕ n) , (m' ⊕ n') 

_-_ : ℤ → ℤ → ℤ
(m , m') - (n , n') = (m ⊕ n') , (m' ⊕ n) 

₀  = zero , zero
₁  = suc zero , zero
-₁ = zero , suc zero

data _≈_ : ℤ → ℤ → Set where
  m≈n : ∀ m m' n n' → (m ⊕ n') ≡ m' ⊕ n → (m , m') ≈ (n , n')

infix 0 _≈_ 

_ : ₁ + -₁ ≈ ₀
_ = m≈n 1 1 zero zero refl 

refl≈ : ∀ p → p ≈ p
refl≈ (m , n) = m≈n m n m n (+-comm m n)

symm≈ : ∀ p q → p ≈ q → q ≈ p
symm≈ .(m , m') .(n , n') (m≈n m m' n n' x) = m≈n n n' m m' lemma
  where
  lemma :  n ⊕ m' ≡ n' ⊕ m
  lemma =
    begin
     n ⊕ m'
    ≡⟨ +-comm n m' ⟩
     m' ⊕ n
    ≡⟨ sym x ⟩
     m ⊕ n'
    ≡⟨ +-comm m n' ⟩
     n' ⊕ m
    ∎


lem1 : ∀ n → n ∸ n ≡ 0
lem1 zero = refl
lem1 (suc n) = lem1 n

lem2 : ∀ m n k → m ⊕ (n ∸ k) ≡ (m ⊕ n) ∸ k
lem2 zero n k = refl
lem2 (suc m) zero k = {!!}
lem2 (suc m) (suc n) k = {!!} 

{-
trans≈ : ∀ p q r → p ≈ q → q ≈ r → p ≈ r
trans≈ .(m , m') .(n , n') .(o , o') (m≈n m m' n n' x) (m≈n .n .n' o o' y) = m≈n m m' o o' Goal where
  Goal : m ⊕ o' ≡ m' ⊕ o
  Goal =
    begin
      m ⊕ o'
    ≡⟨ id-l (m ⊕ o') ⟩
      (m ⊕ o') ⊕ 0
    ≡⟨ sym (cong (_⊕_ (m ⊕ o')) (lem1 n')) ⟩
      (m ⊕ o') ⊕ (n' ∸ n')
    ≡⟨ {!!} ⟩
      (m ⊕ n') ⊕ (o' ∸ n')
    ≡⟨ cong (λ z → z ⊕ (o' ∸ n')) x ⟩
      m' ⊕ n ⊕ (o' ∸ n')
    ≡⟨ {!!} ⟩
    m' ⊕ o ⊕ (n ∸ n')
    ≡⟨ {!!} 
      m' ⊕ o
    ∎
    
-}


trans≈ : ∀ p q r → p ≈ q → q ≈ r → p ≈ r
trans≈ .(m , m') .(n , n') .(o , o') (m≈n m m' n n' x) (m≈n .n .n' o o' y) = m≈n m m' o o' Goal where
  step1 : m ⊕ n' ⊕ (n ⊕ o') ≡ m' ⊕ n ⊕ (n ⊕ o')
  step1 = cong (λ z → z ⊕ (n ⊕ o')) x
  step2 :  m ⊕ n' ⊕ (n ⊕ o') ≡ m ⊕ n ⊕ (n' ⊕ o')
  step2 =
    begin
      m ⊕ n' ⊕ (n ⊕ o')
    ≡⟨ {!!} ⟩
       m ⊕ (n' ⊕ n) ⊕ o'
    ≡⟨ {!!} ⟩
       m ⊕ n ⊕ (n' ⊕ o')
    ∎
    
  Goal : m ⊕ o' ≡ m' ⊕ o
  Goal = begin
    m ⊕ o'
    ≡⟨ {!!} ⟩
    m' ⊕ o ∎
