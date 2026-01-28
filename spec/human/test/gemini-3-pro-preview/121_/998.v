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

Example test_case : problem_121_spec [31; 120; 42; 75; 120; 41; 53; 75; 86; 97; 52; 119; 75; 75; 75; 53] 234.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 203).
  { reflexivity. }
  { reflexivity. }
  (* Index 1: 120. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 2: 42. Even pos, Even val. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* Index 3: 75. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 4: 120. Even pos, Even val. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* Index 5: 41. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 6: 53. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 150).
  { reflexivity. }
  { reflexivity. }
  (* Index 7: 75. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 8: 86. Even pos, Even val. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* Index 9: 97. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 10: 52. Even pos, Even val. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* Index 11: 119. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 12: 75. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 75).
  { reflexivity. }
  { reflexivity. }
  (* Index 13: 75. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 14: 75. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 0).
  { reflexivity. }
  { reflexivity. }
  (* Index 15: 53. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Base case: nil *)
  apply soep_nil.
Qed.