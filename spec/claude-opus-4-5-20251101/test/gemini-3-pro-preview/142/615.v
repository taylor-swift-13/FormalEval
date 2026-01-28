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

Example test_sum_squares : sum_squares_spec [-12%Z; -15%Z; -17%Z; 20%Z; 33%Z; 37%Z; 40%Z; 45%Z; 48%Z; 49%Z; 50%Z; 58%Z; 70%Z; 64%Z; 72%Z; 81%Z; 82%Z; 88%Z; 92%Z; 94%Z; 50%Z; -17%Z; 48%Z] 848180%Z.
Proof.
  unfold sum_squares_spec.
  vm_compute.
  reflexivity.
Qed.