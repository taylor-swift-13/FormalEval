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
    (seq 0%nat (Nat.div (length arr) 2%nat)) 0.

Example test_smallest_change : smallest_change_spec [2; 13; 5; 7; 7; 4; 9; 10; 8; -9; 36; 6; 4; 2; 5; 4; 9] 7.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.