(* HumanEval 60 - Inductive Spec *)
Require Import Coq.Arith.Arith.

Inductive sum_to_n_rel : nat -> nat -> Prop :=
| str_zero : sum_to_n_rel 0%nat 0%nat
| str_step : forall n s, sum_to_n_rel n s -> sum_to_n_rel (S n) (S n + s).

Definition sum_to_n_spec (n : nat) (output : nat) : Prop :=
  sum_to_n_rel n output.


