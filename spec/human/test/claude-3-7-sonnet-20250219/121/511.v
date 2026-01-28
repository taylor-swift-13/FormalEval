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

Example test_sum_odd_in_even_pos : problem_121_spec [22;33;100;65;55;66;56;99;21;0;22;100;33;88] 109.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=22 even? no → false, add 0 *)
  (* idx=1 even? false, skip *)
  (* idx=2 even? true, h=100 even? yes, skip *)
  (* idx=3 even? false, skip *)
  (* idx=4 even? true, h=55 odd? yes, add 55 *)
  (* idx=5 even? false, skip *)
  (* idx=6 even? true, h=56 even? yes, skip *)
  (* idx=7 even? false, skip *)
  (* idx=8 even? true, h=21 odd? yes, add 21 *)
  (* idx=9 even? false, skip *)
  (* idx=10 even? true, h=22 even? yes, skip *)
  (* idx=11 even? false, skip *)
  (* idx=12 even? true, h=33 odd? yes, add 33 *)
  (* idx=13 even? false, skip *)
  (* sum = 0 + 0 + 0 + 0 + 55 + 0 + 0 + 0 + 21 + 0 + 0 + 0 + 33 + 0 = 109 *)
  reflexivity.
Qed.