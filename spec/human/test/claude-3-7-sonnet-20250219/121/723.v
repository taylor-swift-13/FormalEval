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

Example test_sum_odd_in_even_pos : problem_121_spec [0; 1; 2; 3; 10; 4; 5; 6; 7; 8; 1; 2; 2] 13.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even, h=0 even => no add *)
  (* idx=1 odd, no add *)
  (* idx=2 even, h=2 even => no add *)
  (* idx=3 odd, no add *)
  (* idx=4 even, h=10 even => no add *)
  (* idx=5 odd, no add *)
  (* idx=6 even, h=5 odd => add 5 *)
  (* idx=7 odd, no add *)
  (* idx=8 even, h=7 odd => add 7 *)
  (* idx=9 odd, no add *)
  (* idx=10 even, h=1 odd => add 1 *)
  (* idx=11 odd, no add *)
  (* idx=12 even, h=2 even => no add *)
  reflexivity.
Qed.