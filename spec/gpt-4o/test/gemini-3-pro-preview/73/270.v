Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if Z.eqb (nth i arr 0) (nth i arr_reversed 0) then acc else acc + 1)
    (seq 0 (length arr / 2)%nat) 0.

Example test_smallest_change : smallest_change_spec [1; 2; 3; 4; 5; 4; -7; 4; 5; 4; 4; 3; 4; 5; 4; 3; 2; 1] 2.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.