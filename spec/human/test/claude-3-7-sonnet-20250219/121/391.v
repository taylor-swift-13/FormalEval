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

Example test_sum_odd_in_even_pos : problem_121_spec [3;4;6;8;9;31] 12.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [3;4;6;8;9;31] 0
     idx=0 even? true
     h=3 odd? yes (negb (even 3)=true)
     so 3 + sum_odd_in_even_pos_aux [4;6;8;9;31] 1
  *)
  (* idx=1 even? false, add 0 + sum of tail *)
  (* idx=2 even? true, h=8 odd? no, add 0 *)
  (* idx=3 even? false, add 0 *)
  (* idx=4 even? true, h=9 odd? yes, so 9 + sum_odd_in_even_pos_aux [31] 5 *)
  (* idx=5 even? false, add 0 *)
  reflexivity.
Qed.