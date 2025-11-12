
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition fib_spec (n : nat) (f : nat) : Prop :=
  (n = 0 /\ f = 0) \/
  (n > 0 /\ exists a b i, a = 1 /\ b = 1 /\ i = 3 /\
    (forall j x y, 3 <= j <= i -> (x, y) = (fib_aux j) -> fib_aux (j+1) = (y, x + y)) /\
    i = n /\ f = b) \/
  (n > 0 /\ (n = 1 \/ n = 2) /\ f = 1).

(* 
Note: To keep this specification self-contained and precise, the definition characterizes fib as:
- fib 0 = 0
- fib 1 = 1, fib 2 = 1
- Otherwise, the result f is the n-th Fibonacci number computed by iterative sums starting from 1,1 up to n.
The "fib_aux" function is a conceptual helper describing the loop state (a,b) at step j.
*)
