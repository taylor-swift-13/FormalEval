Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.

Definition smallest_change_spec (arr : list Z) (cnt : nat) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if Z.eqb (nth i arr 0%Z) (nth i arr_reversed 0%Z) then acc else acc + 1)
    (seq 0 (length arr / 2)) 0.

Example test_smallest_change : smallest_change_spec [-5; 1; 2; 46; 3; 4; 5; 6; 7; 49; 9; 7; 10; 10; 9; 8; 38; 7; 6; 5; 4; 3; 2; 1; 10; 6]%Z 7.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.