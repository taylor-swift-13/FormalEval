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

Example test_sum_odd_in_even_pos : problem_121_spec [0;1;2;3;4;5;6;7;8;9;10;32;9] 9.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=0 even, so 0 *)
  (* idx=1 odd, skip *)
  (* idx=2 even, h=2 even, skip 0 *)
  (* idx=3 odd, skip *)
  (* idx=4 even, h=4 even, skip 0 *)
  (* idx=5 odd, skip *)
  (* idx=6 even, h=6 even, skip 0 *)
  (* idx=7 odd, skip *)
  (* idx=8 even, h=8 even, skip 0 *)
  (* idx=9 odd, skip *)
  (* idx=10 even, h=10 even, skip 0 *)
  (* idx=11 odd, skip *)
  (* idx=12 even, h=9 odd, add 9 + 0 *)
  reflexivity.
Qed.