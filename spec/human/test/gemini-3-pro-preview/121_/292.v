Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [12; 11; 22; 33; 6; 65; 55; 66; 88; 99; 22; 22; 65; 88] 120.
Proof.
  unfold problem_121_spec.
  apply soep_skip; [ right; reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_skip; [ right; reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_skip; [ right; reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_match with (s_tail := 65); [ reflexivity | reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_skip; [ right; reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_skip; [ right; reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_match with (s_tail := 0); [ reflexivity | reflexivity | ].
  apply soep_skip; [ left; reflexivity | ].
  apply soep_nil.
Qed.