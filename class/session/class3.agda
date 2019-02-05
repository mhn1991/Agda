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
  
lem : {A : Set} → (xs ys : List A) → rev (xs ++ ys) ≡ (rev ys) ++ (rev xs)
lem [] ys =  sym (unit-l (rev ys))
lem (x ∷ xs) ys rewrite cong (λ α → α ++ [ x ]) (lem xs ys)  = {!!} 
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


--Q3
sumR :  List ℕ → ℕ
sumR [] = 0
sumR (x ∷ xs) = x + sumR xs

sumT :  List ℕ → ℕ → ℕ
sumT [] sum = sum
sumT (x ∷ xs) sum = sumT xs (sum + x)

sumApp : List ℕ → ℕ
sumApp [] = 0
sumApp list = sumT list 0

sumF : List ℕ → ℕ
sumF = foldr _+_ 0
--Q4

sumR≡sumF : (xs : List ℕ) → sumR xs ≡ sumF xs
sumR≡sumF [] = refl
sumR≡sumF (x ∷ xs) = cong (_+_ x) (sumR≡sumF xs)

sumR≡sumT : (xs : List ℕ)  → sumR xs ≡ sumApp xs 
sumR≡sumT [] = refl
sumR≡sumT (x ∷ xs) = {!!} 

