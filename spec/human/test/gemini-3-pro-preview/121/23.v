Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example test_problem_121 : problem_121_spec [1; 2; 3; 4; 5] 9.
Proof.
  unfold problem_121_spec.
  unfold sum_odd_in_even_pos_impl.
  (* The simplification tactic evaluates the Fixpoint and boolean conditions:
     idx 0: val 1 (odd), even idx (true) -> include 1
     idx 1: val 2 (even), even idx (false) -> 0
     idx 2: val 3 (odd), even idx (true) -> include 3
     idx 3: val 4 (even), even idx (false) -> 0
     idx 4: val 5 (odd), even idx (true) -> include 5
     Sum: 1 + 0 + 3 + 0 + 5 = 9 *)
  simpl.
  reflexivity.
Qed.