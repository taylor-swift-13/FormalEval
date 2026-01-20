Require Import Arith.
Require Import List.
Require Import Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (index : nat) : nat :=
  match l with
  | [] => 0
  | h :: t =>
    if (Nat.even index) && (negb (Nat.even h))
    then h + sum_odd_in_even_pos_aux t (index + 1)
    else sum_odd_in_even_pos_aux t (index + 1)
  end.

Definition solution_spec (l : list nat) (output : nat) : Prop :=
  l <> [] ->
  output = sum_odd_in_even_pos_aux l 0.

Example solution_test :
  solution_spec [4; 4; 77; 4; 6; 9; 12; 8; 11; 33; 8; 33; 9] 97.
Proof.
  unfold solution_spec.
  intros H.
  simpl.
  reflexivity.
Qed.