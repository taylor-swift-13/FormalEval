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

Example test_case : problem_121_spec [0; 1; 2; 54; 3; 4; 5; 6; 7; 9; 10] 15.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 0 (Even). Skip (Right condition: value is even). *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: Val 1. Skip (Left condition: index is odd). *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: Val 2 (Even). Skip (Right condition: value is even). *)
  apply soep_skip. { right. reflexivity. }
  (* Index 3: Val 54. Skip (Left condition: index is odd). *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: Val 3 (Odd). Match. Need sum 15, current 3, tail sum 12. *)
  apply soep_match with (s_tail := 12). { reflexivity. } { reflexivity. }
  (* Index 5: Val 4. Skip (Left condition: index is odd). *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: Val 5 (Odd). Match. Need sum 12, current 5, tail sum 7. *)
  apply soep_match with (s_tail := 7). { reflexivity. } { reflexivity. }
  (* Index 7: Val 6. Skip (Left condition: index is odd). *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: Val 7 (Odd). Match. Need sum 7, current 7, tail sum 0. *)
  apply soep_match with (s_tail := 0). { reflexivity. } { reflexivity. }
  (* Index 9: Val 9. Skip (Left condition: index is odd). *)
  apply soep_skip. { left. reflexivity. }
  (* Index 10: Val 10 (Even). Skip (Right condition: value is even). *)
  apply soep_skip. { right. reflexivity. }
  (* Index 11: Nil. Base case. *)
  apply soep_nil.
Qed.