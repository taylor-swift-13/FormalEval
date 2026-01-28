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

Example test_case : problem_121_spec [100; 1; 2; 1; 1; 1; 99; 1; 1; 1; 0; 88] 101.
Proof.
  unfold problem_121_spec.
  (* Index 0: 100. Pos 0 (even), Val 100 (even). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: 1. Pos 1 (odd). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: 2. Pos 2 (even), Val 2 (even). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 3: 1. Pos 3 (odd). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: 1. Pos 4 (even), Val 1 (odd). Match. s_tail must be 100. *)
  apply soep_match with (s_tail := 100). { reflexivity. } { reflexivity. }
  (* Index 5: 1. Pos 5 (odd). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: 99. Pos 6 (even), Val 99 (odd). Match. s_tail must be 1. *)
  apply soep_match with (s_tail := 1). { reflexivity. } { reflexivity. }
  (* Index 7: 1. Pos 7 (odd). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: 1. Pos 8 (even), Val 1 (odd). Match. s_tail must be 0. *)
  apply soep_match with (s_tail := 0). { reflexivity. } { reflexivity. }
  (* Index 9: 1. Pos 9 (odd). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 10: 0. Pos 10 (even), Val 0 (even). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 11: 88. Pos 11 (odd). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Nil *)
  apply soep_nil.
Qed.