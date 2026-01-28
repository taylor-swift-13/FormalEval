Require Import List.
Require Import ZArith.
Require Import Arith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if Z.eqb (nth i arr 0) (nth i arr_reversed 0) then acc else acc + 1)
    (seq 0 (Nat.div (length arr) 2%nat)) 0.

Example test_smallest_change : smallest_change_spec [2%Z; 3%Z; 1%Z; 29%Z; -5%Z; 10%Z; 8%Z; 4%Z; 8%Z] 4%Z.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.