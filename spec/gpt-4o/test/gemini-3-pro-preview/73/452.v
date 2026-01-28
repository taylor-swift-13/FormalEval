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
    (seq 0%nat (length arr / 2)%nat) 0.

Example test_smallest_change : smallest_change_spec [-9%Z; -8%Z; -7%Z; -6%Z; -5%Z; 17%Z; -4%Z; -3%Z; -2%Z; -1%Z; 0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 21%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 11%Z.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.