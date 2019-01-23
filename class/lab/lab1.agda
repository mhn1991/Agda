data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data Bool : Set where
  true : Bool
  false : Bool

data Valid : Bool → Set where
  check : Valid true
{-
if_then_else : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

_%_ : Nat → Nat → Nat
n % zero = n
n % (suc m) = mod-helper 0 m n m


is-even : Nat → Bool
is-even n = if (n % 2) == 0 then true else false
-}
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
