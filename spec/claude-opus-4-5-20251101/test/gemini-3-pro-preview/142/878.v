Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition transform_entry (idx : nat) (num : Z) : Z :=
  if (Nat.modulo idx 3 =? 0)%nat then num * num
  else if (Nat.modulo idx 4 =? 0)%nat then num * num * num
  else num.

Fixpoint sum_squares_helper (lst : list Z) (idx : nat) : Z :=
  match lst with
  | [] => 0
  | x :: xs => transform_entry idx x + sum_squares_helper xs (S idx)
  end.

Definition sum_squares_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_squares_helper lst 0.

Example test_sum_squares : sum_squares_spec [0; -6; 14; -1; -11; -4; -4; -4; -4; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 13; -20; -19; -18; -17; -16; -15; -14; -16] (-1643).
Proof.
  unfold sum_squares_spec.
  simpl.
  reflexivity.
Qed.