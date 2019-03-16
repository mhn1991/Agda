open import Data.Nat
open import Relation.Binary.PropositionalEquality

module class7 where

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A
  infixr 10 _::_

  record Stream (A : Set) : Set where
   coinductive
   field
    hd : A
    tl : Stream A
  open Stream public

  upFrom : ℕ → Stream ℕ
  hd (upFrom n) = n
  tl (upFrom n) = upFrom (suc n)

  take : ℕ → {A : Set} → Stream A → List A
  take zero xs = []
  take (suc n) xs = hd xs :: take n (tl xs)

  skip : ℕ → {A : Set} → Stream A → Stream A
  skip zero xs = xs
  skip (suc n) xs = skip n (tl xs)

  buffer : {A : Set} → List A → Stream A → Stream A
  buffer [] ys = ys
  hd (buffer (x :: xs) ys) = x
  tl (buffer (x :: xs) ys) = buffer xs ys

  record _≈_ {A : Set} (xs ys : Stream A) : Set where
   coinductive
   field
    hd-eq : hd xs ≡ hd ys
    tl-eq : tl xs ≈ tl ys
  open _≈_ public

  refl≈ : {A : Set} (xs : Stream A) → xs ≈ xs
  hd-eq (refl≈ xs) = refl {x = hd xs}
  tl-eq (refl≈ xs) = refl≈ (tl xs)

  trans≈ : {A : Set} {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  hd-eq (trans≈ p q) = trans (hd-eq p) (hd-eq q)
  tl-eq (trans≈ p q) = trans≈ (tl-eq p) (tl-eq q)

-- Question 1
  toSeq : {A : Set} → Stream A → (ℕ → A)
  toSeq xs = λ x → hd (skip x xs)


  fromSeq : {A : Set} → (ℕ → A) → Stream A
  hd (fromSeq f) = f zero
  tl (fromSeq f) = fromSeq (λ x → f (suc x))


  lem : {A : Set} (xs : Stream A) → fromSeq (λ x → toSeq xs (suc x)) ≈ tl xs
  hd-eq (lem xs)  = refl
  tl-eq (lem xs) = lem (tl xs)

  fromtoSeq : {A : Set} (xs : Stream A) → fromSeq (toSeq xs) ≈ xs
  hd-eq (fromtoSeq xs) = refl
  tl-eq (fromtoSeq xs) = lem xs

-- Question 2

  eqn : ∀ {A : Set} (xs : Stream A) n → buffer (take n xs) (skip n xs) ≈ xs
  eqn xs zero = refl≈ xs
  eqn xs (suc n) = eqn-aux xs n where
    eqn-aux : ∀ {A : Set} (xs : Stream A) n → buffer (hd xs :: take n (tl xs)) (skip n (tl xs)) ≈ xs
    hd-eq (eqn-aux xs zero) = refl
    hd-eq (eqn-aux xs (suc n)) = refl
    tl-eq (eqn-aux xs zero) = refl≈ (tl xs)
    tl-eq (eqn-aux xs (suc n)) = eqn-aux ((tl xs)) n


-- Question 3
-- (begin by replacing the postulate below by a type definition)

  record All  {A : Set} (P : A → Set) (xs : Stream A) : Set where
    coinductive
    field
      hd-eq' : P (hd xs)
      tl-eq' : All P (tl xs)
  open All public

  lem' : (m : ℕ) → (m > 0) → All (λ n → n > 0) (upFrom m)
  hd-eq' (lem' zero ())
  hd-eq' (lem' (suc m) P) = s≤s z≤n 
  tl-eq' (lem' zero ())
  tl-eq' (lem' (suc m) P ) = lem' ((suc (suc m))) (s≤s z≤n)

  fact : All (\n → n > 0) (upFrom 1)
  fact = lem' 1 (s≤s z≤n)
