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

Example test_sum_odd_in_even_pos : problem_121_spec [1; 0; 1; 2; 54; 3; 4; 5; 6; 7; 9; 10] 11.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [1;0;1;2;54;3;4;5;6;7;9;10] 0
     idx=0 even? true
     h=1 odd? yes
     so 1 + sum_odd_in_even_pos_aux [0;1;2;54;3;4;5;6;7;9;10] 1
  *)
  (* idx=1 even? false, add 0 + sum ... *)
  (* idx=2 even? true, h=1 odd? yes, add 1 + ... *)
  (* idx=3 even? false, add 0 + ... *)
  (* idx=4 even? true, h=54 even? no contribution *)
  (* idx=5 even? false, add 0 + ... *)
  (* idx=6 even? true, h=4 even? no contribution *)
  (* idx=7 even? false, add 0 + ... *)
  (* idx=8 even? true, h=6 even? no contribution *)
  (* idx=9 even? false, add 0 + ... *)
  (* idx=10 even? true, h=9 odd? yes, add 9 + ... *)
  (* idx=11 even? false, add 0 *)
  reflexivity.
Qed.