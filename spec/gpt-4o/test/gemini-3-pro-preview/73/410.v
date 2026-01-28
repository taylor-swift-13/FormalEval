Require Import List.
Require Import Arith.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = Z.of_nat (fold_left (fun acc i =>
    if Z.eqb (nth i arr 0) (nth i arr_reversed 0) then acc else (acc + 1)%nat)
    (seq 0 (length arr / 2)%nat) 0%nat).

Example test_smallest_change : smallest_change_spec [3; 2; 5; -9; 1; 6; 7; 9; 10; 41; 6; 4; 8; 1] 7.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.