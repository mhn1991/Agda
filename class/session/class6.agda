open import Data.Product

Rel : Set → Set₁
Rel A = A → A → Set

data Lex {A B : Set} (R : Rel A) (S : Rel B) : Rel (A × B) where
  lex-fst : ∀ {a1 a2 b1 b2} → R a1 a2 → Lex R S (a1 , b1) (a2 , b2)
  lex-snd : ∀ a {b1 b2} → S b1 b2 → Lex R S (a , b1) (a , b2)


--Q1

Trans : ∀ {a} → Rel a → Set
Trans P = ∀ {i j k} → P i j → P j k → P i k

Transitive : {A B : Set} (R : Rel A) (S : Rel B) → Trans R → Trans S → Trans (Lex R S)
Transitive R S TR TS {i} {j} {k} (lex-fst x) (lex-fst x₁) = lex-fst (TR x x₁)
Transitive R S TR TS {i} {j} {k} (lex-fst x) (lex-snd a x₁) = lex-fst x
Transitive R S TR TS {i} {j} {k} (lex-snd a x) (lex-fst x₁) = lex-fst x₁
Transitive R S TR TS {i} {j} {k} (lex-snd a x) (lex-snd .a x₁) = lex-snd a (TS x x₁)

--Q2
open import Relation.Binary.PropositionalEquality
data ⊥ : Set where
¬_ : Set → Set
¬_ A = A → ⊥

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

Decidable : {A : Set} → Rel A → Set
Decidable R = ∀ a1 a2 → Dec (R a1 a2)

dec : {A B : Set} (R : Rel A) (S : Rel B) →  Decidable R → Decidable S → Decidable {A} (_≡_) → Decidable (Lex R S) 
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) with DA fst₁ fst₁ | DS snd₁ snd₁
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | yes P₁  | yes P = yes (lex-fst {!!})
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | yes P₁  | no ¬P = yes {!!}
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | no ¬P₁  | yes P = no (λ _ → ¬P₁ refl)
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | no ¬P₁  | no ¬P = no (λ _ → ¬P₁ refl)

--Q3

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
    acc : (∀ y → y < x  → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (A → A → Set) → Set
WellFounded _<_ = ∀ x → Acc _<_ x


lexwel : {A B : Set} (R : Rel A) (S : Rel B) → WellFounded R → WellFounded S →  WellFounded (Lex R S)
lexwel R S WR WS P = acc λ y x → acc λ y₁ x₁ → {!!}
