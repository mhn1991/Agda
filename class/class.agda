open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
{-
data Bool : Set where
  true : Bool
  false : Bool
-}
data Valid : Bool → Set where
  check : Valid true

check-eq : Nat → Nat → Bool
check-eq zero zero = true
check-eq (suc m) (suc n) = check-eq m n
check-eq _ _ = false

_ : Valid(check-eq (suc zero) (suc zero))
_ = check

if_then_else : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

_%_ : Nat → Nat → Nat
n % zero = n
n % (suc m) = mod-helper 0 m n m


is-even : Nat → Bool
is-even n = if (n % 2) == 0 then true else false

even : Nat → Bool
even zero = true
even (suc(suc n)) = even n
even _ = false

not : Bool → Bool
not true = false
not false = true

p1 : ∀ n → Valid (even n) → Valid (not (even (suc n)))
p1 zero _ = check
p1 (suc zero) ()
p1 (suc (suc n)) p = p1 n p


eq : ∀ n → Valid (check-eq n n)
eq zero = check 
eq (suc n) = eq n


sym-eq-ck : ∀ m n → Valid (check-eq m n) → Valid (check-eq n m)
sym-eq-ck zero zero _ = check
sym-eq-ck (suc m) (suc n) p = sym-eq-ck m n p
sym-eq-ck zero (suc _) ()
sym-eq-ck (suc _) zero ()

