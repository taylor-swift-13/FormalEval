Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if (nth i arr 0) =? (nth i arr_reversed 0) then acc else acc + 1)
    (seq 0%nat (length arr / 2)%nat) 0.

Example test_smallest_change : smallest_change_spec [-10; -8; -8; 2; -5; -4; -3; -2; -1; -9; 1; 2; 3; 3; 5; 6; 7; 9; 10; -3; 6; 1; -7; -5; 1] 12.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.