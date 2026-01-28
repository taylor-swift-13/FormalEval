Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if Z.eqb (nth i arr 0%Z) (nth i arr_reversed 0%Z) then acc else (acc + 1)%Z)
    (seq 0 (length arr / 2)) 0%Z.

Example test_smallest_change : smallest_change_spec [3%Z; 2%Z; 5%Z; (-8)%Z; 1%Z; 6%Z; 7%Z; 9%Z; 10%Z; 41%Z; 6%Z; 4%Z; 8%Z] 6%Z.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.