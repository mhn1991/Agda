import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)


record _⇔_ (A B : Set) : Set where
  field
    f : A → B
    g : B → A
    fg : ∀ (b : B) → f (g b) ≡ b
    gf : ∀ (a : A) → g (f a) ≡ a

postulate
  ext : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g
             
data ⊤ : Set where
  • : ⊤

data ⊥ : Set where

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

infix 2 _,_


{-- Intro end elim rules --}

{- Conjunction -}

∧I : {A B : Set} → A → B → A ∧ B
∧I a b = a , b

∧El : {A B : Set} → A ∧ B → A
∧El (a , _) = a

∧Er : {A B : Set} → A ∧ B → B
∧Er (_ , b) = b


{- Disjunction-}

∨Ir : {A B : Set} → B → A ∨ B
∨Ir b = inr b

∨Il : {A B : Set} → A → A ∨ B
∨Il A = inl A

∨E : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
∨E (inl a) f g = f a
∨E (inr b) f g = g b 

{- Implication -}

→E : {A B : Set} → (A → B) → A → B
→E f a = f a

→E′ : {A B : Set} → (A → B) → A → B
→E′ f = f

→E″ : {A B : Set} → (A → B) → A → B
→E″ = λ f → f

→I : {A B : Set} → B → (A → B)
→I b = λ _ → b

→I′ : {A B : Set} → B → (A → B)
→I′ b _ = b

_ : {A B : Set} → →E {A} {B} ≡ →E′ 
_ = refl

_ : {A B : Set} → →E′ {A} {B} ≡ →E″
_ = refl

{- Boolean laws / isos ? -}

-- Isos are more powerful than logical equivalence:

_↭_ : Set → Set → Set
A ↭ B = (A → B) ∧ (B → A)

_ : {A B : Set} → A ⇔ B → (A ↭ B)
_ = λ i → (λ a → _⇔_.f i a) , (λ b → _⇔_.g i b)

unit⊥ : {A : Set} → (⊥ ∧ A) ⇔ ⊥
unit⊥ {A} = record { f  = λ {  ( () , _  ) }
               ; g  = λ ()
               ; gf = λ {  ( () , _  ) }
               ; fg = λ ()
               }
{-
unit⊤ : {A : Set} → (A ∨ ⊤) ⇔ ⊤
unit⊤ {A} = record { f = λ _ → • ; g = λ _ → inr • ; fg = Goal₀ ; gf = {!!} } where
  Goal₀ : (b : ⊤) → • ≡ b
  Goal₀ • = refl
  Goal : (a : A ∨ ⊤) → inr • ≡ a
  Goal (inl x) = {! Goal: inr • ≡ inl x!} {- Proof relevance! Hegel (1807): All the same, while proof is essential in the case of mathematical knowledge, it still does not have the significance and nature of being a moment in the result itself. -}
  Goal (inr •) = refl 
-}

{- Negation -}

EFQ : {A : Set} → ⊥ → A
EFQ ()

¬ : Set → Set
¬ A = A → ⊥

¬¬⊤ : ¬ (¬ ⊤)
¬¬⊤ f = f • 


{- Not even "logically" -}

postulate DNE : {A : Set} → ¬ (¬ A) → A


LEM : {A : Set} → A ∨ ¬ A
LEM  = {!!} 

Bool→ : {A B : Set} → (A → B) → ¬ A ∨ B
Bool→ = {!!}

Bool→' : {A B : Set} → ¬ A ∨ B → A → B
Bool→' = {!!} 

{- Algebra of exponentials, e.g. (ab)ᶜ = (aᶜ)(bᶜ) -}

→∧Law : {A B C : Set} → (C → A ∧ B) ⇔ ((C → A) ∧ (C → B))
→∧Law {A} {B} {C} = {!!}

{- Universal quantifier -}

∀E : ∀ {D : Set} {P : D → Set}
   → (A : ∀ (x : D) → P(x) )
   → (a : D)
   → P a
∀E A a = A a


{- Existential quantifier -}

  

{- 
Exercises:
* Boolean laws vs. Algebraic laws with exponentiation
* DNI, TNE, 
* A → (A → B), (A → B) → A ⊢ B
* LEM <-> DNE
* Bool→ <-> LEM/DNE
-}
