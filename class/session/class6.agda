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

helper : {A B : Set} (fst : A) (snd snd₁ : B) (R : Rel A) (S : Rel B)
         -> (S snd snd₁ → ⊥ ) -> (R fst fst → ⊥)
         -> ¬ (Lex R S (fst , snd) (fst , snd₁))
helper fst snd snd1 R S ¬P1 ¬P (lex-fst x) = ¬P x
helper fst snd snd1 R S ¬P1 ¬P (lex-snd .fst x) = ¬P1 x

helper1 : {A B : Set} (fst fst₁ : A) (snd snd₁ : B) (R : Rel A) (S : Rel B)
          -> (S snd snd₁ ) -> (R fst fst₁ → ⊥) -> ¬ (fst ≡ fst₁)
          -> ¬ (Lex R S (fst , snd) (fst₁ , snd₁)) 
helper1 fst fst₁ snd snd₁ R S P1 ¬P ¬P2 (lex-fst x) = ¬P x
helper1 fst .fst snd snd₁ R S P1 ¬P ¬P2 (lex-snd .fst x) = ¬P2 refl


helper2 : {A B : Set} (fst fst₁ : A) (snd snd₁ : B) (R : Rel A) (S : Rel B)
          -> (¬ S snd snd₁) -> (R fst fst₁ → ⊥) -> ¬ (fst ≡ fst₁)
          -> ¬ (Lex R S (fst , snd) (fst₁ , snd₁))
helper2 fst fst₁ snd snd₁ R S ¬P1 ¬P ¬P2 (lex-fst x) = ¬P x
helper2 fst .fst snd snd₁ R S ¬P1 ¬P ¬P2 (lex-snd .fst x) = ¬P2 refl


dec : {A B : Set} (R : Rel A) (S : Rel B) →  Decidable R → Decidable S → Decidable {A} (_≡_) → Decidable (Lex R S)
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) with DR fst fst₁
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | yes P = yes (lex-fst P)
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | no ¬P  with DS snd snd₁ | DA fst fst₁
dec R S DR DS DA (fst , snd) (.fst , snd₁) | no ¬P | yes P1 | yes refl = yes (lex-snd fst P1)
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | no ¬P | no ¬P1 | yes refl = no λ x → helper fst snd snd₁ R S ¬P1 ¬P x
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | no ¬P | yes P1 | no ¬P2 = no (λ x → helper1 fst fst₁ snd snd₁ R S P1 ¬P ¬P2 x)
dec R S DR DS DA (fst , snd) (fst₁ , snd₁) | no ¬P | no ¬P1 | no ¬P2 = no (λ x → helper2 fst fst₁ snd snd₁ R S ¬P1 ¬P ¬P2 x)




--Q3
data Acc {A : Set} (_<_ : A → A → Set) (x : A) : Set where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (A → A → Set) → Set
WellFounded _<_ = ∀ x → Acc _<_ x


wf-Lex : {A B : Set} {R : Rel A} {S : Rel B} → WellFounded R → WellFounded S → WellFounded (Lex R S)
wf-Lex {R = R}{S = S} wfr wfs (a , b) = acc (lemma a b (wfr a) (wfs b))
  where
    lemma : ∀ a b → Acc R a → Acc S b → ∀ y → Lex R S y (a , b) → Acc (Lex R S) y
    lemma a b (acc ar) _ (a1 , b1) (lex-fst p) = acc (lemma a1 b1 (ar a1 p) (wfs b1))
    lemma a b ar (acc as) (.a , b1) (lex-snd .a p) = acc (lemma a b1 ar (as b1 p))
