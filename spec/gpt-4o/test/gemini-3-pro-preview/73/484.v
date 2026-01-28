Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0%nat (length arr / 2)%nat) 0.

Example test_smallest_change : smallest_change_spec [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; -4; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; -5; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 13; 49; 50] 25.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.