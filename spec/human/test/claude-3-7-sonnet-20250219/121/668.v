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

Example test_sum_odd_in_even_pos : problem_121_spec [100;1;2;1;1;1;99;1;1;1;0;88] 101.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=100 even? yes (Nat.even 100 = true), so 0 added *)
  (* idx=1 even? false, no addition *)
  (* idx=2 even? true, h=2 even? yes, add 0 *)
  (* idx=3 odd, no addition *)
  (* idx=4 even? true, h=1 odd? yes, add 1 *)
  (* idx=5 odd, no addition *)
  (* idx=6 even? true, h=99 odd? yes, add 99 *)
  (* idx=7 odd, no addition *)
  (* idx=8 even? true, h=1 odd? yes, add 1 *)
  (* idx=9 odd, no addition *)
  (* idx=10 even? true, h=0 even? yes, add 0 *)
  (* idx=11 odd, no addition *)
  reflexivity.
Qed.