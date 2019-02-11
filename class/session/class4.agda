import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym)
open import Function using (_∘_)

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


{- Negation -}

EFQ : {A : Set} → ⊥ → A
EFQ ()

¬ : Set → Set
¬ A = A → ⊥

¬¬⊤ : ¬ (¬ ⊤)
¬¬⊤ f = f • 


{- Not even "logically" -}

postulate DNE : {A : Set} → ¬ (¬ A) → A


{- Algebra of exponentials, e.g. (ab)ᶜ = (aᶜ)(bᶜ) -}
{-
→∧Law : {A B C : Set} → (C → A ∧ B) ⇔ ((C → A) ∧ (C → B))
→∧Law {A} {B} {C} = record {
  f = λ x → (λ y → ∧El (→E x y)) , (λ z → ∧Er (→E x z)) ;
  g = λ x y →  ∧I (→E (∧El x) y) (→E (∧Er x) y) ;
  fg =  λ b → {!!};
  gf = λ a → {!!} }
    
-}
--v1 :  {A B C : Set} → (C → A ∧ B) → (C → A) ∧ (C → B)


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

--Q1
LEM : {A : Set} → A ∨ ¬ A 
LEM  = DNE (λ z → z (inr (λ x → z (inl x))))

Bool→ : {A B : Set} → (A → B) → ¬ A ∨ B
Bool→ f = DNE (λ b → b (inl (λ x → b (inr (f x))))) 

Bool→' : {A B : Set} → ¬ A ∨ B → A → B
Bool→' (inl a)  = λ z → DNE (λ _ → a z)
Bool→' (inr b) = →I b

--Q2
-- ⇔ and ∧ has same infixr I increase ∧ infixr to avoid parentesis
infixr 21 _∧_
∧comm : ∀ {A B : Set} → A ∧ B ⇔ B ∧ A
∧comm = record {
  f = λ{(x , y) → y , x } ;
  g = λ{ ( y , x ) → ( x , y ) } ;
  fg = λ{ ( x , y ) → refl } ;
  gf = λ{ ( y , x ) → refl } }

∧assoc : ∀ {A B C : Set} → (A ∧ B) ∧ C ⇔ A ∧ (B ∧ C)
∧assoc =
  record
    { f      = λ{ (( x , y ) , z ) → ( x , ( y , z )) }
    ; g    = λ{ ( x , ( y , z )) → (( x , y ) , z ) }
    ; gf = λ{ (( x , y ) , z ) → refl }
    ; fg = λ{ ( x , ( y , z )) → refl }
    }
--id 
⊤-idl : ∀ {A : Set} → ⊤ ∧ A ⇔ A
⊤-idl =
  record
    { f   = λ{ ( • , x ) → x }
      ; g = λ{ x → ( • , x ) }
    ; gf  = λ{ ( • , x )  → refl }
    ; fg  = λ{ x → refl }
    }

⊤-idr : ∀ {A : Set} → A ∧ ⊤  ⇔ A
⊤-idr =
  record
    { f   = λ{ ( x , • ) → x }
      ; g = λ{ x → ( x , • ) }
    ; gf  = λ{ ( x , • )  → refl }
    ; fg  = λ{ x → refl }
    }

--(p ^ n) ^ m  ≡  p ^ (n * m)
^* : ∀ {A B C : Set} → (A → B → C) ⇔ (A ∧ B → C)
^* =
  record
    { f  =  λ{ f → λ{ (x , y ) → f x y }}
    ; g  =  λ{ g → λ{ x → λ{ y → g ( x , y ) }}}
    ; gf =  λ{ f → refl }
    ; fg =  λ{ g → ext λ{ ( x , y ) → refl }}
    }

--(p * n) ^ m = (p ^ m) * (n ^ m)

∧dis : ∀ {A B : Set} (w : A ∧ B) → ( ∧El w , ∧Er w ) ≡ w
∧dis ( x , y ) = refl

→^*distrib : ∀ {A B C : Set} → (A → B ∧ C) ⇔ (A → B) ∧ (A → C)
→^*distrib =
  record
    { f    = λ{ f → ( ∧El ∘ f , ∧Er ∘ f ) }
    ; g    = λ{ ( k , l ) → λ{ x → ( k x , l x ) } }
    ; gf   = λ{ f → ext λ{ x → ∧dis (f x) } }
    ; fg   = λ{ ( g , h ) → refl }
    }


--p ^ (n + m) = (p ^ n) * (p ^ m)
→∨dis : ∀ {A B C : Set} → (A ∨ B → C) ⇔ ((A → C) ∧ (B → C))
→∨dis =
  record
    { f  = λ{ f → ( f ∘ inl , f ∘ inr ) }
    ; g  = λ{ ( k , l ) → λ{ (inl x) → k x ; (inr y) → l y } }
    ; gf = λ{ f → ext λ{ (inl x) → refl ; (inr y) → refl } }
    ; fg = λ{ ( g , h ) → refl }
    }
