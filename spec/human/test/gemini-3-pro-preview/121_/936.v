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

Example test_case : problem_121_spec [1; 1; 96; 55; 1; 0; 1; 22; 2; 1; 1; 1; 1; 1; 55; 2; 1] 61.
Proof.
  unfold problem_121_spec.
  (* Index 0: 1. Even pos, Odd val. Match. Need 61 = 1 + 60. *)
  apply soep_match with (s_tail := 60). reflexivity. reflexivity.
  (* Index 1: 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: 96. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 3: 55. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: 1. Even pos, Odd val. Match. Need 60 = 1 + 59. *)
  apply soep_match with (s_tail := 59). reflexivity. reflexivity.
  (* Index 5: 0. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 6: 1. Even pos, Odd val. Match. Need 59 = 1 + 58. *)
  apply soep_match with (s_tail := 58). reflexivity. reflexivity.
  (* Index 7: 22. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 8: 2. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 9: 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 10: 1. Even pos, Odd val. Match. Need 58 = 1 + 57. *)
  apply soep_match with (s_tail := 57). reflexivity. reflexivity.
  (* Index 11: 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 12: 1. Even pos, Odd val. Match. Need 57 = 1 + 56. *)
  apply soep_match with (s_tail := 56). reflexivity. reflexivity.
  (* Index 13: 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 14: 55. Even pos, Odd val. Match. Need 56 = 55 + 1. *)
  apply soep_match with (s_tail := 1). reflexivity. reflexivity.
  (* Index 15: 2. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 16: 1. Even pos, Odd val. Match. Need 1 = 1 + 0. *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Nil *)
  apply soep_nil.
Qed.