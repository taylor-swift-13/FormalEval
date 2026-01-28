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

Example test_sum_odd_in_even_pos : problem_121_spec [2;11;3;3;88;6;9;8;11;10;8;3;2;2] 23.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even, h=2 even -> 0 + sum of tail *)
  (* idx=1 odd -> skip *)
  (* idx=2 even, h=3 odd -> 3 + ... *)
  (* idx=3 odd -> skip *)
  (* idx=4 even, h=88 even -> skip *)
  (* idx=5 odd -> skip *)
  (* idx=6 even, h=9 odd -> 9 + ... *)
  (* idx=7 odd -> skip *)
  (* idx=8 even, h=11 odd -> 11 + ... *)
  (* idx=9 odd -> skip *)
  (* idx=10 even, h=8 even -> skip *)
  (* idx=11 odd -> skip *)
  (* idx=12 even, h=2 even -> skip *)
  (* idx=13 odd -> skip *)
  reflexivity.
Qed.