(* HumanEval 36 - Inductive Spec *)
Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Inductive digit_7_count_rel : nat -> nat -> Prop :=
| d7c_zero : digit_7_count_rel 0%nat 0%nat
| d7c_mod10_7 : forall n c, n mod 10 = 7 ->
   digit_7_count_rel (n / 10) c -> digit_7_count_rel n (S c)
| d7c_mod10_other : forall n c, n mod 10 <> 7 ->
   digit_7_count_rel (n / 10) c -> digit_7_count_rel n c.

Inductive range_7_count_rel : nat -> nat -> Prop :=
| r7c_zero : range_7_count_rel 0%nat 0%nat
| r7c_div11 : forall i c, (i mod 11 =? 0) = true \/ (i mod 13 =? 0) = true ->
   digit_7_count_rel i c -> range_7_count_rel i c
| r7c_no_div : forall i c, (S i mod 11 =? 0) = false /\ (S i mod 13 =? 0) = false ->
   range_7_count_rel i c -> range_7_count_rel (S i) c.

Definition fizz_buzz_spec (n : nat) (output : nat) : Prop :=
  range_7_count_rel n output.

