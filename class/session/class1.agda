data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data Bool : Set where
  true : Bool
  false : Bool

data Valid : Bool → Set where
  check : Valid true

check-eq : Nat → Nat → Bool
check-eq zero zero = true
check-eq (suc m) (suc n) = check-eq m n
check-eq _ _ = false

_ : Valid(check-eq (suc zero) (suc zero))
_ = check

eq : ∀ n → Valid (check-eq n n)
eq zero = check 
eq (suc n) = eq n


sym-eq-ck : ∀ m n → Valid (check-eq m n) → Valid (check-eq n m)
sym-eq-ck zero zero _ = check
sym-eq-ck (suc m) (suc n) p = sym-eq-ck m n p
sym-eq-ck zero (suc _) ()
sym-eq-ck (suc _) zero ()

