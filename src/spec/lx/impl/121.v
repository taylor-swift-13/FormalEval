Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

Example sum_odd_in_even_pos_impl_ex: sum_odd_in_even_pos_impl (5%nat :: 8%nat :: 7%nat :: 1%nat :: nil) = 12%nat.
Proof. reflexivity. Qed.

Definition sum_odd_in_even_pos_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.


