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
  solution_spec [31; 96; 3; 120; 42; 53; 75; 86; 97; 52; 119; 75; 75; 75] 400.
Proof.
  unfold solution_spec.
  intros H.
  simpl.
  reflexivity.
Qed.