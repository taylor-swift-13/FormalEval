(* """ Return list of prime factors of given integer in the order from smallest to largest.
Each of the factors should be listed number of times corresponding to how many times it appeares in factorization.
Input number should be equal to the product of all factors
>>> factorize(8)
[2, 2, 2]
>>> factorize(25)
[5, 5]
>>> factorize(70)
[2, 5, 7]
""" *)

(* Spec(input : int, output : list int) :=

​	IsSorted(output) ∧

​	Multiply(output) = input ∧

​	∀i ∈ output, IsPrime(i) *)


Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.


Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition Is_Sorted(l : list nat) : Prop :=
  forall i j : nat,
    i < j /\ j < length l -> nth i l 0 <= nth j l 0.

(* Pre: no additional constraints for `factorize` by default *)
Definition Pre (input : nat) : Prop := True.

Definition Spec (input : nat) (output : list nat) : Prop :=
  Is_Sorted output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.