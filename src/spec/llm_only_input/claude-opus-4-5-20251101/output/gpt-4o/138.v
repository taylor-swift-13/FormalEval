Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

(* Function that checks if a number can be expressed as sum of two positive even numbers *)
Definition is_equal_to_sum_even (n : nat) : bool :=
  (8 <=? n) && Nat.even n.

(* Convert Z to nat for the test *)
Definition is_equal_to_sum_even_Z (z : Z) : bool :=
  is_equal_to_sum_even (Z.to_nat z).

Example test_is_equal_to_sum_even_4 : is_equal_to_sum_even_Z 4%Z = false.
Proof.
  unfold is_equal_to_sum_even_Z.
  unfold is_equal_to_sum_even.
  simpl.
  reflexivity.
Qed.