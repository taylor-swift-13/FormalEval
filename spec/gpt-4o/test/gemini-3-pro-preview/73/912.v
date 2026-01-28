Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition smallest_change_spec (arr : list nat) (cnt : nat) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0 (length arr / 2)) 0.

Example test_smallest_change : smallest_change_spec [1; 2; 3; 4; 5; 6; 7; 8; 40; 9; 2; 11; 12; 13; 15; 16; 17; 18; 20] 9.
Proof.
  unfold smallest_change_spec.
  (* Evaluate the computation on the right hand side *)
  vm_compute.
  (* The goal reduces to 9 = 9 *)
  reflexivity.
Qed.