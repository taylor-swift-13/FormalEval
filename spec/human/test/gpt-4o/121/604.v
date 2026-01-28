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

Example test_case_1 : problem_121_spec [11; 22; 32; 44; 65; 55; 66; 3; 88; 99; 22; 22] 76.
Proof.
  unfold problem_121_spec.
  unfold sum_odd_in_even_pos_impl.
  unfold sum_odd_in_even_pos_aux.
  simpl.
  (* idx = 0, h = 11, not added *)
  (* idx = 1, h = 22, not added *)
  (* idx = 2, h = 32, not added *)
  (* idx = 3, h = 44, not added *)
  (* idx = 4, h = 65, added *)
  (* idx = 5, h = 55, not added *)
  (* idx = 6, h = 66, not added *)
  (* idx = 7, h = 3, not added *)
  (* idx = 8, h = 88, not added *)
  (* idx = 9, h = 99, added *)
  (* idx = 10, h = 22, not added *)
  (* idx = 11, h = 22, not added *)
  simpl. reflexivity.
Qed.