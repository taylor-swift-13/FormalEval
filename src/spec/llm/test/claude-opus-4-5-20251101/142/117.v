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

Example test_sum_squares : sum_squares_spec [3%Z; 6%Z; 1%Z; 7%Z; 0%Z; 8%Z; -9%Z; -3%Z; 10%Z; 11%Z] 1272%Z.
Proof.
  unfold sum_squares_spec.
  unfold sum_squares_helper.
  unfold transform_entry.
  simpl.
  reflexivity.
Qed.