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

Example test_sum_odd_in_even_pos : problem_121_spec [11;22;33;44;54;66;88;99;22;22;66;33;22;22;22;33] 44.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even, h=11 odd => 11 + ... *)
  (* idx=1 odd => 0 + ... *)
  (* idx=2 even, h=33 odd => 33 + ... *)
  (* idx=3 odd => 0 + ... *)
  (* idx=4 even, h=54 even => 0 + ... *)
  (* idx=5 odd => 0 + ... *)
  (* idx=6 even, h=88 even => 0 + ... *)
  (* idx=7 odd => 0 + ... *)
  (* idx=8 even, h=22 even => 0 + ... *)
  (* idx=9 odd => 0 + ... *)
  (* idx=10 even, h=66 even => 0 + ... *)
  (* idx=11 odd => 0 + ... *)
  (* idx=12 even, h=22 even => 0 + ... *)
  (* idx=13 odd => 0 + ... *)
  (* idx=14 even, h=22 even => 0 + ... *)
  (* idx=15 odd => 0 + ... *)
  (* sum is 11 + 33 = 44 *)
  reflexivity.
Qed.