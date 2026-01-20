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

Example test_sum_squares : sum_squares_spec [-16%Z; -9%Z; -2%Z; 36%Z; 36%Z; 26%Z; -20%Z; 25%Z; -40%Z; 20%Z; -4%Z; 12%Z; -26%Z; 35%Z; 37%Z] (-14196%Z).
Proof.
  unfold sum_squares_spec.
  unfold sum_squares_helper.
  unfold transform_entry.
  simpl.
  reflexivity.
Qed.