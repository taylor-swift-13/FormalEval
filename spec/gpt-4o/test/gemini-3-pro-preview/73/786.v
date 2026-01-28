Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0 (length arr / 2)%nat) 0.

Example test_smallest_change : smallest_change_spec [1; 2; 3; 46; 5; 6; -3; 7; 17; 8; 9; 10; 11; 12; 13; 14; 15; 17; 19; -8; 14] 10.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.