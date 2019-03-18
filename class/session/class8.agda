open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

-- In Q1 we make use of the standard definition of lists...
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

-- ...and in Q1 and Q2 we make use of the standard definition of leaf-labelled binary trees...

data Bin (A : Set) : Set where
  L : A → Bin A
  N : Bin A → Bin A → Bin A

-- Q1
-- Recall that the standard operations "append" and "flatten" can be defined as follows in direct-style:
{- 
append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

flatten : {A : Set} → Bin A → List A
flatten (L x) = x :: []
flatten (N t1 t2) = append (flatten t1) (flatten t2)
-}

-- Rewrite append and flatten in continuation-passing style to eliminate all non-tail calls.
-- You should begin by defining functions "append-cps" and "flatten-cps" of the following (polymorphic) types...

append-cps : {A : Set} → List A → List A → {R : Set} → (List A → R) → R
append-cps [] ys k = k ys
append-cps (x :: xs) ys k = append-cps xs ys (λ p → k (x :: p))

flatten-cps : {A : Set} → Bin A → {R : Set} → (List A → R) → R
flatten-cps (L x) k = k (x :: [])
flatten-cps (N t1 t2) k = flatten-cps t1 (λ p → flatten-cps t2 (λ p2 → append-cps p p2 k ))

-- ...then call append-cps and flatten-cps with appropriate continuations to recover the original operations:
append : {A : Set} → List A → List A → List A
append xs ys = append-cps xs ys (λ p → p)

flatten : {A : Set} → Bin A → List A
flatten t = flatten-cps t (λ p → p)

-- Q2

-- In this question you will use continuation-passing style to define an operation of "grafting" one binary tree onto a branch
-- of another (cf. https://en.wikipedia.org/wiki/Grafting).

-- Given two binary trees t and u and a natural number n, "left-graft t u n" is defined as the binary tree that results
-- from picking the nth subtree of u -- call it "v" -- and replacing it by "N t v".  Here subtrees of u are numbered
-- according to a preorder traversal (see https://en.wikipedia.org/wiki/Tree_traversal#Pre-order_(NLR)), starting at 0 (which
-- corresponds to the tree u itself).  Moreover, the index n should be less than the total number of subtrees or else the
-- grafting operation will fail.  That is, we want to define a function of the following type:
{-
left-graft : {A : Set} → Bin A → Bin A → ℕ → Maybe (Bin A)
-}

-- In order to define left-graft, you will write a function "left-graft-cps t u n ks kf" that takes *two* continuations:
-- the first continuation ks (accepting a binary tree) is to be used in case of a successful graft, the second
-- continuation kf (accepting a natural number) is to be used in case the index n runs out of bounds of u.

-- Here is a skeleton for left-graft-cps (we have already filled in the n=0 case):
left-graft-cps : {A : Set} → Bin A → Bin A → ℕ → {R : Set} → (Bin A → R) → (ℕ → R) → R
left-graft-cps t u zero ks kf = ks (N t u)
left-graft-cps t (L t1) (suc n) ks kf = {!!}
left-graft-cps t (N t1 t2) (suc n) ks kf = left-graft-cps t t1 n ks kf

-- You do not need to write much code here... the difficulty is just figuring out which code to write!

-- Finally, finish implementing left-graft by calling left-graft-cps with the appropriate continuations:
left-graft : {A : Set} → Bin A → Bin A → ℕ → Maybe (Bin A)
left-graft t u n = {!!}

-- Some test cases showing all of the ways to left-graft the tree "N (L 0) (L 0)" into the
-- tree "N (N (L 1) (L 2)) (L 3)" (which has 5 subtrees)
{-
t = N (L 0) (L 0)
u = N (N (L 1) (L 2)) (L 3)

_ : left-graft t u 0 ≡ just (N (N (L 0) (L 0)) (N (N (L 1) (L 2)) (L 3)))
_ = refl

_ : left-graft t u 1 ≡ just (N (N (N (L 0) (L 0)) (N (L 1) (L 2))) (L 3))
_ = refl

_ : left-graft t u 2 ≡ just (N (N (N (N (L 0) (L 0)) (L 1)) (L 2)) (L 3))
_ = refl

_ : left-graft t u 3 ≡ just (N (N (L 1) (N (N (L 0) (L 0)) (L 2))) (L 3))
_ = refl

_ : left-graft t u 4 ≡ just (N (N (L 1) (L 2)) (N (N (L 0) (L 0)) (L 3)))
_ = refl

_ : left-graft t u 5 ≡ nothing
_ = refl

-}

-- Q3
-- For this question we consider a simple language of arithmetic expressions augmented with a
-- C/C++/Java-style counter:

data Exp : Set where
  num : ℕ → Exp
  add mul : Exp → Exp → Exp
  x++ : Exp

-- If we ignored "x++", then the semantics of expressions would be very simple indeed.
-- Evaluation could be defined in direct-style like so:
{-
eval : Exp → ℕ
eval (num n) = n
eval (add e1 e2) = eval e1 + eval e2
eval (mul e1 e2) = eval e1 * eval e2
-}

-- Luckily, things are not so simple! The intended semantics of "x++" (as in C/C++/Java) is that it
-- returns the value of the variable x, with the side-effect of incrementing x.  Moreover, in order
-- for the value of an expression with multiple occurrences of "x++" to be well-defined, we specify
-- that the variable x is originally set to 0, and that evaluation proceeds from left-to-right.

-- Here are some examples of expressions with their intended semantics:
-- [add x++ x++]                                        should evaluate to 1
-- [add (mul (num 0) (num 2)) (mul (num 1) (num 3))]    should evaluate to 3
-- [add (mul x++ (num 2)) (mul x++ (num 3))]            should evaluate to 3
-- [add (mul x++ (num 3)) (mul x++ (num 2))]            should evaluate to 2
-- [mul (add (num 2) x++) (add x++ x++)]                should evaluate to 6
-- [mul (add x++ x++) (add (num 2) x++)]                should evaluate to 4

-- Define the "eval" function for the full language by first writing a function "eval-cps e x k", which takes
-- as extra arguments the current value of the variable x, as well as a continuation k that expects to be called
-- with two arguments: the value of e and the updated value of the variable x.
-- (We've already filled in the first case of eval-cps below, where e is a number.)

eval-cps : Exp → ℕ → {R : Set} → (ℕ → ℕ → R) → R
eval-cps (num n) x k = k n x
eval-cps (add e1 e2) x k = eval-cps e1 x (λ p1 s1 → eval-cps e2 s1 (λ p2 s2 → k (p1 + p2) s2))
eval-cps (mul e1 e2) x k = eval-cps e1 x (λ p1 s1 → eval-cps e2 s1 (λ p2 s2 → k (p1 * p2) s2))
eval-cps (x++) x k = k x (suc x) 

eval : Exp → ℕ
eval e = eval-cps e zero (λ m n → m)


_ : eval (add x++ x++) ≡ 1
_ = refl

_ : eval (add (mul (num 0) (num 2)) (mul (num 1) (num 3))) ≡ 3
_ = refl

_ : eval (add (mul x++ (num 2)) (mul x++ (num 3))) ≡ 3
_ = refl

_ : eval (add (mul x++ (num 3)) (mul x++ (num 2))) ≡ 2
_ = refl

_ : eval (mul (add (num 2) x++) (add x++ x++)) ≡ 6
_ = refl

_ : eval (mul (add x++ x++) (add (num 2) x++)) ≡ 4
_ = refl
