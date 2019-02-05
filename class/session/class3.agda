{-
1-State and prove the induction principle for lists.
2-Use rewrite to make lemma₀, lemma₁, and idrev more concise (if possible).
3-Compute the sum of all elements of a list using
  *a recursive function
  *a tail-recursive function
  *fold
4-Show the functions defined above return the same values.
-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.List
open import Data.Nat
open import Data.Product


induction-ℕ : (P : ℕ → Set) → (P zero) → (∀ n → P n → P (1 + n)) → (∀ n → P n)
induction-ℕ P IB IS zero = IB
induction-ℕ P IB IS (suc n) = induction-ℕ (λ z → P (suc z)) (IS zero IB) (λ n₁ → IS (suc n₁)) n 

zero-unit-+ : ∀ n → n + 0 ≡ n
zero-unit-+ zero = refl
zero-unit-+ (suc n) = cong suc (zero-unit-+ n) 

zero-unit-+' : ∀ n → n + 0 ≡ n
zero-unit-+' n = induction-ℕ (λ n → n + 0 ≡ n) refl (λ _ n → cong suc n) n 

-- List concatenation is a monoid

unit-r : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
unit-r xs = refl

unit-l : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
unit-l [] = refl
unit-l (x ∷ xs) = cong (_∷_ x) (unit-l xs) 

assoc : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
assoc [] ys zs = refl
assoc (x ∷ xs) ys zs = cong (_∷_ x) (assoc xs ys zs)

rev : {A : Set} → (xs : List A) → List A
rev [] = []
rev (x ∷ xs) = (rev xs) ++ [ x ]

-- rev is involutive
lemma₀ : {A : Set} → (xs : List A) (y : A) → rev (xs ++ [ y ]) ≡ [ y ] ++ (rev xs)
lemma₀ [] y = refl
lemma₀ (x ∷ xs) y = Goal where
  IH :   rev (xs ++ [ y ])          ≡ y ∷ rev xs 
  IH = lemma₀ xs y
  Goal : rev (xs ++ [ y ]) ++ [ x ] ≡ (y ∷ rev xs) ++ [ x ]
  Goal = cong (λ α → α ++ [ x ]) IH
   
lemma₁ : {A : Set} → (xs ys : List A) → rev (xs ++ ys) ≡ (rev ys) ++ (rev xs)
lemma₁ [] ys = sym (unit-l (rev ys))
lemma₁ (x ∷ xs) ys = Goal where
  IH : rev (xs ++ ys) ≡ (rev ys) ++ (rev xs)
  IH = lemma₁ xs ys
  Goal : rev (xs ++ ys) ++ [ x ] ≡ rev ys ++ (rev xs ++ [ x ])
  Goal = begin
         rev (xs ++ ys) ++ [ x ]
       ≡⟨ cong (λ α → α ++ [ x ]) IH ⟩
         (rev ys ++ rev xs) ++ [ x ]
       ≡⟨ assoc (rev ys) (rev xs) (x ∷ []) ⟩
         rev ys ++ (rev xs ++ [ x ])
       ∎
  
idrev : {A : Set} → (xs : List A) → rev (rev xs) ≡ xs
idrev [] = refl
idrev (x ∷ xs) = Goal where
  IH : rev (rev xs) ≡ xs
  IH = idrev xs
  Goal : rev (rev xs ++ [ x ]) ≡ x ∷ xs
  Goal = begin
         rev (rev xs ++ [ x ])
       ≡⟨ lemma₁ (rev xs) [ x ] ⟩
         x ∷ rev (rev xs)
       ≡⟨ cong (λ α → x ∷ α) IH ⟩ 
         x ∷ xs
       ∎
-- Correctness of tail-recursive reverse

-- If as a where clause this causes proof problems
revapp : {A : Set} → (xs acc : List A) → List A
revapp [] acc = acc
revapp (x ∷ xs) acc = revapp xs (x ∷ acc)

trev : {A : Set} → (xs : List A) → List A
trev xs = revapp xs [] 

lemma : {A : Set} → (xs ys zs : List A) → (revapp xs ys) ++ zs ≡ revapp xs (ys ++ zs)
lemma [] ys zs = refl
lemma (x ∷ xs) ys zs = lemma xs (x ∷ ys) zs
  
rev≡trev' : {A : Set} → (xs : List A) → rev xs ≡ trev xs
rev≡trev' [] = refl
rev≡trev' (x ∷ xs) = Goal where
  IH : rev xs ≡ revapp xs []
  IH = rev≡trev' xs
  Goal' : (revapp xs []) ++ [ x ] ≡ revapp xs [ x ]
  Goal' = lemma xs [] (x ∷ [])
  Goal : rev xs ++ [ x ] ≡ revapp xs [ x ]
  Goal = begin
         rev xs ++ [ x ] ≡⟨ cong (λ α → α ++ [ x ]) IH ⟩
         (revapp xs []) ++ [ x ] ≡⟨ Goal' ⟩
         revapp xs [ x ] ∎

rev≡trev : {A : Set} → (xs : List A) → rev xs ≡ trev xs
rev≡trev [] = refl
rev≡trev (x ∷ xs) rewrite cong (λ α → α ++ [ x ]) (rev≡trev xs) = lemma xs [] [ x ] 
--Q1
induction-list : {A : Set} → (P : List A → Set) → (P []) → ((x : A) (xs : List A) → P xs → P(x ∷ xs)) → (xs : List A) → P xs
induction-list P IB IS [] = IB
induction-list P IB IS (x ∷ xs) = IS x xs (induction-list P IB IS xs)
--Q2
lem₀ : {A : Set} → (xs : List A) (y : A) → rev (xs ++ [ y ]) ≡ [ y ] ++ (rev xs)
lem₀ [] y = refl
lem₀ (x ∷ xs) y rewrite cong (λ α → α ++ [ x ]) (lem₀ xs y) = refl

lem₁ : {A : Set} → (xs ys : List A) → rev (xs ++ ys) ≡ (rev ys) ++ (rev xs)
lem₁ [] ys =  sym (unit-l (rev ys))
lem₁ (x ∷ xs) ys rewrite cong (λ α → α ++ [ x ]) (lem₁ xs ys) | assoc (rev ys) (rev xs) (x ∷ []) = refl
--Q3
sumR :  List ℕ → ℕ
sumR [] = 0
sumR (x ∷ xs) = x + sumR xs

sumT :  List ℕ → ℕ → ℕ
sumT [] sum = sum
sumT (x ∷ xs) sum = sumT xs (x + sum)

sumF : List ℕ → ℕ
sumF = foldr _+_ 0
--Q4
+-assoc : ∀ m n r → m + n + r ≡ m + (n + r)
+-assoc zero n r = refl
+-assoc (suc m) n r = cong suc (+-assoc m n r)

id-l : ∀ n → n ≡ n + zero
id-l zero = refl
id-l (suc n) = cong suc (id-l n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero n = id-l n
+-comm (suc m) n = lem m n
  where
    lem : ∀ m n → suc m + n ≡ n + suc m
    lem m zero = cong suc (sym (id-l m))
    lem m (suc n) = let IH = lem m n in
                    trans (cong suc (let p = lem n m in trans (sym p) (cong suc (+-comm n m)))) (cong suc IH)


ch :  (xs : List ℕ) (m n : ℕ) → (sumT xs m) + n ≡ sumT xs (m + n)
ch [] m n = refl
ch (x ∷ xs) m n rewrite ch xs (x + m) n = cong (sumT xs) (+-assoc x m n)

lem1 : ∀ m n → suc m ≡ suc n → m ≡ n
lem1 m .m refl = refl

lem2 : ∀ m n r → r + m ≡ r + n → m ≡ n
lem2 m n zero p = p
lem2 m n (suc r) p = lem2 m n r (lem1 (r + m) (r + n) p)

sumR≡sumF : (xs : List ℕ) → sumR xs ≡ sumF xs
sumR≡sumF [] = refl
sumR≡sumF (x ∷ xs) = cong (_+_ x) (sumR≡sumF xs)

sumR≡sumT : (xs : List ℕ) → sumR xs ≡ sumT xs 0 
sumR≡sumT [] = refl
sumR≡sumT (x ∷ xs) rewrite +-comm x 0  | sym (ch xs 0 x) | +-comm x (sumR xs) | cong (λ z → z + x) (sumR≡sumT xs)  = refl 
