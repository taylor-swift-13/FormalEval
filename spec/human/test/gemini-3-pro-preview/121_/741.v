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

Example test_case : problem_121_spec [0; 1; 2; 3; 4; 5; 6; 7; 8; 1; 2; 0] 0.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 0 (even), Pos 0 (even). Skip (val even). *)
  apply soep_skip. right. reflexivity.
  (* Index 1: Val 1, Pos 1 (odd). Skip (pos odd). *)
  apply soep_skip. left. reflexivity.
  (* Index 2: Val 2 (even), Pos 2 (even). Skip (val even). *)
  apply soep_skip. right. reflexivity.
  (* Index 3: Val 3, Pos 3 (odd). Skip (pos odd). *)
  apply soep_skip. left. reflexivity.
  (* Index 4: Val 4 (even), Pos 4 (even). Skip (val even). *)
  apply soep_skip. right. reflexivity.
  (* Index 5: Val 5, Pos 5 (odd). Skip (pos odd). *)
  apply soep_skip. left. reflexivity.
  (* Index 6: Val 6 (even), Pos 6 (even). Skip (val even). *)
  apply soep_skip. right. reflexivity.
  (* Index 7: Val 7, Pos 7 (odd). Skip (pos odd). *)
  apply soep_skip. left. reflexivity.
  (* Index 8: Val 8 (even), Pos 8 (even). Skip (val even). *)
  apply soep_skip. right. reflexivity.
  (* Index 9: Val 1, Pos 9 (odd). Skip (pos odd). *)
  apply soep_skip. left. reflexivity.
  (* Index 10: Val 2 (even), Pos 10 (even). Skip (val even). *)
  apply soep_skip. right. reflexivity.
  (* Index 11: Val 0, Pos 11 (odd). Skip (pos odd). *)
  apply soep_skip. left. reflexivity.
  (* Nil *)
  apply soep_nil.
Qed.