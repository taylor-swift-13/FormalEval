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

Example test_problem_121 : problem_121_spec [2; 3; 5; 13; 5] 10.
Proof.
  unfold problem_121_spec.
  unfold sum_odd_in_even_pos_impl.
  (* The simplification tactic evaluates the Fixpoint and boolean conditions:
     idx 0: val 2 (even), even idx (true) -> 0
     idx 1: val 3 (odd), even idx (false) -> 0
     idx 2: val 5 (odd), even idx (true) -> include 5
     idx 3: val 13 (odd), even idx (false) -> 0
     idx 4: val 5 (odd), even idx (true) -> include 5
     Sum: 0 + 0 + 5 + 0 + 5 = 10 *)
  simpl.
  reflexivity.
Qed.