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

Example test_sum_odd_in_even_pos : problem_121_spec [0; 2; 3; 77; 67; 6; 8; 9; 10] 70.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [0;2;3;77;67;6;8;9;10] 0
     idx=0 even? true, h=0 even? yes, so 0 + sum_odd_in_even_pos_aux [2;3;77;67;6;8;9;10] 1
  *)
  (* idx=1 even? false, add 0 + ... *)
  (* idx=2 even? true, h=3 odd? yes, so 3 + sum_odd_in_even_pos_aux [77;67;6;8;9;10] 3 *)
  (* idx=3 even? false, add 0 + ... *)
  (* idx=4 even? true, h=67 odd? yes, so 67 + sum_odd_in_even_pos_aux [6;8;9;10] 5 *)
  (* idx=5 even? false, add 0 + ... *)
  (* idx=6 even? true, h=8 even? yes, add 0 + sum_odd_in_even_pos_aux [9;10] 7 *)
  (* idx=7 even? false, add 0 + sum_odd_in_even_pos_aux [10] 8 *)
  (* idx=8 even? true, h=10 even? yes, add 0 + sum_odd_in_even_pos_aux [] 9 *)
  reflexivity.
Qed.