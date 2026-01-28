Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = Z.of_nat (fold_left (fun acc i =>
    if Z.eqb (nth i arr 0) (nth i arr_reversed 0) then acc else S acc)
    (seq 0%nat (Nat.div (length arr) 2)) 0%nat).

Example test_smallest_change : smallest_change_spec [-10; -9; -8; -7; -6; 32; 27; -3; -1; -9; 1; 2; 3; 3; 5; -9; 6; 7; -6; 31; 8; 9; 10; -3; -7; 8] 12.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.