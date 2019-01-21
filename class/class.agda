data Bool : Set where
  true : Bool
  false : Bool

data Valid : Bool → Set where
  check : Valid true

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

check-eq : Nat → Nat → Bool
check-eq zero zero = true
check-eq (suc m) (suc n) = check-eq m n
check-eq _ _ = false

_ : Valid(check-eq (suc zero) (suc zero))
_ = check
