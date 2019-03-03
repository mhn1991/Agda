open import Data.Product

Rel : Set → Set₁
Rel A = A → A → Set

data Lex {A B : Set} (R : Rel A) (S : Rel B) : Rel (A × B) where
  lex-fst : ∀ {a1 a2 b1 b2} → R a1 a2 → Lex R S (a1 , b1) (a2 , b2)
  lex-snd : ∀ a {b1 b2} → S b1 b2 → Lex R S (a , b1) (a , b2)




--Q1

Trans : ∀ {a} → Rel a → Rel a → Rel a → Set
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

Transitive : {a : Set} → Rel a → Set
Transitive _∼_ = Trans _∼_ _∼_ _∼_

Transitive' : {A B : Set} (R : Rel A) (S : Rel B) → Transitive R → Transitive S → Transitive (Lex R S)
Transitive' R S TR TS P = {!!}



--Q2

data ⊥ : Set where
¬_ : Set → Set
¬_ A = A → ⊥

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

Decidable : {A : Set} → Rel A → Set
Decidable R = ∀ a1 a2 → Dec (R a1 a2)

dec : {A B : Set} (R : Rel A) (S : Rel B) →  Decidable R → Decidable S → Decidable (Lex R S) 
dec R S DR DS = {!!}



--Q3

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
    acc : (∀ y → y < x  → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (A → A → Set) → Set
WellFounded _<_ = ∀ x → Acc _<_ x


lexwel : {A B : Set} (R : Rel A) (S : Rel B) → WellFounded R → WellFounded S →  WellFounded (Lex R S)
lexwel = {!!}
