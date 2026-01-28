Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = Z.of_nat (fold_left (fun acc i =>
    if Z.eqb (nth i arr 0) (nth i arr_reversed 0) then acc else S acc)
    (seq 0 (Nat.div (length arr) 2)) 0%nat).

Example test_smallest_change : smallest_change_spec [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 13; 26; -3; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 41; 43; 44; 45; 46; 48; 49; 50; 13; -7; 35; 6] 25.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.