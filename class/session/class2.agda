import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _⊕_)
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


--  Q1 
+-assoc : ∀ m n r → m ⊕ n ⊕ r ≡ m ⊕ (n ⊕ r)
+-assoc zero n r = refl
+-assoc (suc m) n r = cong suc (+-assoc m n r)

lem1 : ∀ m n → suc m ≡ suc n → m ≡ n
lem1 m .m refl = refl

lem2 : ∀ m n r → r ⊕ m ≡ r ⊕ n → m ≡ n
lem2 m n zero p = p
lem2 m n (suc r) p = lem2 m n r (lem1 (r ⊕ m) (r ⊕ n) p)

trans≈ : ∀ p q r → p ≈ q → q ≈ r → p ≈ r
trans≈ .(m , m') .(n , n') .(r , r') (m≈n m m' n n' p1) (m≈n .n .n' r r' p2) = m≈n m m' r r' Goal
  where
    prf1 : m ⊕ r' ⊕ (n' ⊕ n) ≡ m' ⊕ r ⊕ (n' ⊕ n)
    prf1 = begin
           m ⊕ r' ⊕ (n' ⊕ n)    ≡⟨ +-assoc m r' (n' ⊕ n) ⟩
           m ⊕ (r' ⊕ (n' ⊕ n))  ≡⟨ cong (λ ◻ → m ⊕ ◻) (sym (+-assoc r' n' n)) ⟩
           m ⊕ (r' ⊕ n' ⊕ n)    ≡⟨ sym (cong (λ z → m ⊕ (z ⊕ n)) (+-comm n' r')) ⟩
           m ⊕ (n' ⊕ r' ⊕ n)    ≡⟨ cong (_⊕_ m) (+-assoc n' r' n) ⟩
           m ⊕ (n' ⊕ (r' ⊕ n))  ≡⟨ sym (+-assoc m n' (r' ⊕ n)) ⟩
           m ⊕ n' ⊕ (r' ⊕ n)    ≡⟨ sym (cong (_⊕_ (m ⊕ n')) (+-comm n r')) ⟩
           m ⊕ n' ⊕ (n ⊕ r')    ≡⟨ cong (λ z → z ⊕ (n ⊕ r')) p1 ⟩
           m' ⊕ n ⊕ (n ⊕ r')    ≡⟨ cong (_⊕_ (m' ⊕ n)) p2 ⟩
           m' ⊕ n ⊕ (n' ⊕ r)    ≡⟨ sym (cong (_⊕_ (m' ⊕ n)) (+-comm r n')) ⟩
           m' ⊕ n ⊕ (r ⊕ n')    ≡⟨ +-assoc m' n (r ⊕ n') ⟩
           m' ⊕ (n ⊕ (r ⊕ n'))  ≡⟨ sym (cong (_⊕_ m') (+-assoc n r n')) ⟩
           m' ⊕ (n ⊕ r ⊕ n')    ≡⟨ sym (cong (λ z → m' ⊕ (z ⊕ n')) (+-comm r n)) ⟩
           m' ⊕ (r ⊕ n ⊕ n')    ≡⟨ cong (_⊕_ m') (+-assoc r n n') ⟩
           m' ⊕ (r ⊕ (n ⊕ n'))  ≡⟨ sym (+-assoc m' r (n ⊕ n')) ⟩
           m' ⊕ r ⊕ (n ⊕ n')    ≡⟨ sym (cong (_⊕_ (m' ⊕ r)) (+-comm n' n)) ⟩          
           m' ⊕ r ⊕ (n' ⊕ n)
           ∎ 
    Goal : m ⊕ r' ≡ m' ⊕ r
    Goal = lem2 (m ⊕ r') (m' ⊕ r) (n' ⊕ n) (trans (+-comm (n' ⊕ n) (m ⊕ r')) (trans prf1 (+-comm (m' ⊕ r) (n' ⊕ n))))


--  Q2
{-
  What we want to prove is cong≈ : ∀ (f : ℤ → ℤ) {x y} → x ≈ y → f x ≈ f y. 
  However lets consider a function
  f : ℤ → ℤ
  f (m , n) = m , zero
  suppose we have (a , a') ≈ (b , b') with a ≢ b, after applying f to both sides, 
  we would have (a , zero) and (b , zero) which are not necessarily equal. 
  Thus we have created a counter example of the congruence rule. 
-}


--  Q3
open import Data.List

infix 2 _isPrefixOf_
data _isPrefixOf_ {A : Set} : List A → List A → Set where
  base : ∀ l → [] isPrefixOf l
  step : ∀ x l1 l2 → l1 isPrefixOf l2 → x ∷ l1 isPrefixOf x ∷ l2

pre-refl : ∀ {A} (l : List A) → l isPrefixOf l
pre-refl [] = base []
pre-refl (x ∷ l) = step x l l (pre-refl l)

pre-antisym : ∀ {A} (l1 l2 : List A) → l1 isPrefixOf l2 → l2 isPrefixOf l1 → l1 ≡ l2
pre-antisym .[] .[] (base .[]) (base .[]) = refl
pre-antisym .(x ∷ l1) .(x ∷ l2) (step x l1 l2 p1) (step .x .l2 .l1 p2) = sym (cong (_∷_ x) (pre-antisym l2 l1 p2 p1))

pre-trans : ∀ {A} (l1 l2 l3 : List A) → l1 isPrefixOf l2 → l2 isPrefixOf l3 → l1 isPrefixOf l3
pre-trans [] l2 l3 p1 p2 = base l3
pre-trans (x ∷ l1) .(x ∷ l2) .(x ∷ l3) (step .x .l1 l2 p1) (step .x .l2 l3 p2) = step x l1 l3 (pre-trans l1 l2 l3 p1 p2)

