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

Example test_case : problem_121_spec [1; 2; 1; 1; 1; 1; 1; 1; 1; 44; 1; 1] 6.
Proof.
  unfold problem_121_spec.
  (* i=0, val=1. Even pos, Odd val. Match. Need sum 5 from tail. *)
  apply soep_match with (s_tail := 5); [reflexivity | reflexivity |].
  (* i=1, val=2. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* i=2, val=1. Even pos, Odd val. Match. Need sum 4 from tail. *)
  apply soep_match with (s_tail := 4); [reflexivity | reflexivity |].
  (* i=3, val=1. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* i=4, val=1. Even pos, Odd val. Match. Need sum 3 from tail. *)
  apply soep_match with (s_tail := 3); [reflexivity | reflexivity |].
  (* i=5, val=1. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* i=6, val=1. Even pos, Odd val. Match. Need sum 2 from tail. *)
  apply soep_match with (s_tail := 2); [reflexivity | reflexivity |].
  (* i=7, val=1. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* i=8, val=1. Even pos, Odd val. Match. Need sum 1 from tail. *)
  apply soep_match with (s_tail := 1); [reflexivity | reflexivity |].
  (* i=9, val=44. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* i=10, val=1. Even pos, Odd val. Match. Need sum 0 from tail. *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity |].
  (* i=11, val=1. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* i=12, nil. *)
  apply soep_nil.
Qed.