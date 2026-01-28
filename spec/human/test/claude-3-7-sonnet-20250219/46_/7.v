Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

(* Using the provided fib4_at definition from the specification *)
Inductive fib4_at : nat -> nat -> Prop :=
| fib4_at_0 : fib4_at 0 0
| fib4_at_1 : fib4_at 1 0
| fib4_at_2 : fib4_at 2 2
| fib4_at_3 : fib4_at 3 0
| fib4_at_SSSS : forall i a b c d,
    fib4_at i a ->
    fib4_at (S i) b ->
    fib4_at (S (S i)) c ->
    fib4_at (S (S (S i))) d ->
    fib4_at (S (S (S (S i)))) (a + b + c + d).

Example fib4_at_3_is_0 : fib4_at 3 0.
Proof.
  apply fib4_at_3.
Qed.

(* Bonus: Proof for fib4_at 6 = 8 *)
Example fib4_at_6_is_8 : fib4_at 6 8.
Proof.
  apply fib4_at_SSSS with (a:=2) (b:=0) (c:=2) (d:=4).
  - apply fib4_at_2.
  - apply fib4_at_3.
  - apply fib4_at_SSSS with (a:=0) (b:=0) (c:=2) (d:=0).
    + apply fib4_at_0.
    + apply fib4_at_1.
    + apply fib4_at_2.
    + apply fib4_at_3.
  - apply fib4_at_SSSS with (a:=0) (b:=2) (c:=0) (d:=2).
    + apply fib4_at_1.
    + apply fib4_at_2.
    + apply fib4_at_3.
    + apply fib4_at_SSSS with (a:=0) (b:=0) (c:=2) (d:=0).
      * apply fib4_at_0.
      * apply fib4_at_1.
      * apply fib4_at_2.
      * apply fib4_at_3.
Qed.

(* Bonus: Proof for fib4_at 7 = 14 *)
Example fib4_at_7_is_14 : fib4_at 7 14.
Proof.
  apply fib4_at_SSSS with (a:=0) (b:=2) (c:=4) (d:=8).
  - apply fib4_at_3.
  - apply fib4_at_SSSS with (a:=0) (b:=0) (c:=2) (d:=0).
    + apply fib4_at_0.
    + apply fib4_at_1.
    + apply fib4_at_2.
    + apply fib4_at_3.
  - apply fib4_at_SSSS with (a:=0) (b:=2) (c:=0) (d:=2).
    + apply fib4_at_1.
    + apply fib4_at_2.
    + apply fib4_at_3.
    + apply fib4_at_SSSS with (a:=0) (b:=0) (c:=2) (d:=0).
      * apply fib4_at_0.
      * apply fib4_at_1.
      * apply fib4_at_2.
      * apply fib4_at_3.
  - apply fib4_at_6_is_8.
Qed.