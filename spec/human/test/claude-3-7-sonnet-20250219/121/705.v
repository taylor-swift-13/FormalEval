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

Example test_sum_odd_in_even_pos : problem_121_spec [1;2;1;1;119;88;1;1] 122.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=1 odd? yes, so 1 + ... *)
  (* idx=1 even? false, add 0 + ... *)
  (* idx=2 even? true, h=1 odd? yes, so 1 + ... *)
  (* idx=3 even? false, add 0 + ... *)
  (* idx=4 even? true, h=119 odd? yes, so 119 + ... *)
  (* idx=5 even? false, add 0 + ... *)
  (* idx=6 even? true, h=1 odd? yes, so 1 + ... *)
  (* idx=7 even? false, add 0 *)
  reflexivity.
Qed.