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

Example test_case : problem_121_spec [0; 1; 44; 4; 5; 6; 7; 66; 3] 15.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Even pos, Even val. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* Index 1: Value 1. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 2: Value 44. Even pos, Even val. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* Index 3: Value 4. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 4: Value 5. Even pos, Odd val. Match. Need 15 - 5 = 10. *)
  apply soep_match with (s_tail := 10).
  { reflexivity. }
  { reflexivity. }
  (* Index 5: Value 6. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 6: Value 7. Even pos, Odd val. Match. Need 10 - 7 = 3. *)
  apply soep_match with (s_tail := 3).
  { reflexivity. }
  { reflexivity. }
  (* Index 7: Value 66. Odd pos. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* Index 8: Value 3. Even pos, Odd val. Match. Need 3 - 3 = 0. *)
  apply soep_match with (s_tail := 0).
  { reflexivity. }
  { reflexivity. }
  (* Index 9: Empty list. *)
  apply soep_nil.
Qed.