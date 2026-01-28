Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example test_case_2 : problem_121_spec [1; 1; 2; 1; 0; 1; 1; 1; 1; 1; 1] 3.
Proof.
  unfold problem_121_spec.
  unfold sum_odd_in_even_pos_impl.
  unfold sum_odd_in_even_pos_aux.
  simpl.
  (* idx = 0, h = 1, added *)
  (* idx = 1, h = 1, not added *)
  (* idx = 2, h = 2, not added *)
  (* idx = 3, h = 1, added *)
  (* idx = 4, h = 0, not added *)
  (* idx = 5, h = 1, not added *)
  (* idx = 6, h = 1, added *)
  (* idx = 7, h = 1, not added *)
  (* idx = 8, h = 1, not added *)
  (* idx = 9, h = 1, not added *)
  (* idx = 10, h = 1, not added *)
  simpl. reflexivity.
Qed.