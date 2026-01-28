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

Example test_sum_odd_in_even_pos : problem_121_spec [11;22;33;44;54;66;88;99;22;22;4;22;22] 44.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=11 odd? yes, so 11 + ... *)
  (* idx=1 even? false, skip 22 *)
  (* idx=2 even? true, h=33 odd? yes, so 33 + ... *)
  (* idx=3 even? false, skip 44 *)
  (* idx=4 even? true, h=54 even, skip *)
  (* idx=5 even? false, skip 66 *)
  (* idx=6 even? true, h=88 even, skip *)
  (* idx=7 even? false, skip 99 *)
  (* idx=8 even? true, h=22 even, skip *)
  (* idx=9 even? false, skip 22 *)
  (* idx=10 even? true, h=4 even, skip *)
  (* idx=11 even? false, skip 22 *)
  (* idx=12 even? true, h=22 even, skip *)
  reflexivity.
Qed.