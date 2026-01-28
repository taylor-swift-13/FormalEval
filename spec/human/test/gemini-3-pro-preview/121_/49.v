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

Example test_case : problem_121_spec [2; 7; 1; 2; 3; 1; 11; 13; 2; 1; 2; 2] 15.
Proof.
  unfold problem_121_spec.
  (* Index 0: 2. Even pos, even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 1: 7. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: 1. Even pos, odd val. Match. 1 + 14 = 15. *)
  apply soep_match with (s_tail := 14). reflexivity. reflexivity.
  (* Index 3: 2. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: 3. Even pos, odd val. Match. 3 + 11 = 14. *)
  apply soep_match with (s_tail := 11). reflexivity. reflexivity.
  (* Index 5: 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 6: 11. Even pos, odd val. Match. 11 + 0 = 11. *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 7: 13. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 8: 2. Even pos, even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 9: 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 10: 2. Even pos, even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 11: 2. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 12: nil. *)
  apply soep_nil.
Qed.