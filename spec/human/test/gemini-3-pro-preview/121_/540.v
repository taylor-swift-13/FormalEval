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

Example test_case : problem_121_spec [11; 53; 22; 33; 44; 65; 55; 66; 88; 56; 99; 0; 22; 33; 88] 165.
Proof.
  unfold problem_121_spec.
  (* Index 0: 11. Even pos, Odd val. Match. Need 11 + 154 = 165. *)
  apply soep_match with (s_tail := 154); [reflexivity | reflexivity |].
  (* Index 1: 53. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 2: 22. Even pos, Even val. Skip. *)
  apply soep_skip; [right; reflexivity |].
  (* Index 3: 33. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 4: 44. Even pos, Even val. Skip. *)
  apply soep_skip; [right; reflexivity |].
  (* Index 5: 65. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 6: 55. Even pos, Odd val. Match. Need 55 + 99 = 154. *)
  apply soep_match with (s_tail := 99); [reflexivity | reflexivity |].
  (* Index 7: 66. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 8: 88. Even pos, Even val. Skip. *)
  apply soep_skip; [right; reflexivity |].
  (* Index 9: 56. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 10: 99. Even pos, Odd val. Match. Need 99 + 0 = 99. *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity |].
  (* Index 11: 0. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 12: 22. Even pos, Even val. Skip. *)
  apply soep_skip; [right; reflexivity |].
  (* Index 13: 33. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 14: 88. Even pos, Even val. Skip. *)
  apply soep_skip; [right; reflexivity |].
  (* Index 15: Nil. *)
  apply soep_nil.
Qed.