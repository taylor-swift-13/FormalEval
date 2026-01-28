Require Import List.
Require Import ZArith.
Require Import Arith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if Z.eqb (nth i arr 0) (nth i arr_reversed 0) then acc else acc + 1)
    (seq 0%nat (Nat.div (length arr) 2)) 0.

Example test_smallest_change : smallest_change_spec [-10; -9; -8; -7; -6; -5; -4; -3; -2; -8; -1; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; -8] 11.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.