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

Example test_sum_odd_in_even_pos : problem_121_spec [0;1;2;3;4;6;7;97;9;2] 16.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=0 odd? no (0 even), add 0 + sum from idx=1 *)
  (* idx=1 even? false, add 0 + sum from idx=2 *)
  (* idx=2 even? true, h=2 odd? no, add 0 + sum from idx=3 *)
  (* idx=3 even? false, add 0 + sum from idx=4 *)
  (* idx=4 even? true, h=4 odd? no, add 0 + sum from idx=5 *)
  (* idx=5 even? false, add 0 + sum from idx=6 *)
  (* idx=6 even? true, h=7 odd? yes, add 7 + sum from idx=7 *)
  (* idx=7 even? false, add 0 + sum from idx=8 *)
  (* idx=8 even? true, h=9 odd? yes, add 9 + sum from idx=9 *)
  (* idx=9 even? false, add 0 *)
  reflexivity.
Qed.