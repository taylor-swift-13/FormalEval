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

Example test_sum_odd_in_even_pos : problem_121_spec [2;5;10;11;11] 11.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [2;5;10;11;11] 0
     idx=0 even? true
     h=2 even? yes (negb (even 2) = false)
     so 0 + sum_odd_in_even_pos_aux [5;10;11;11] 1
  *)
  (* idx=1 even? false, add 0 + sum of tail *)
  (* idx=2 even? true, h=10 even? yes no add *)
  (* idx=3 even? false add 0 *)
  (* idx=4 even? true h=11 odd? yes so 11 + 0 *)
  reflexivity.
Qed.