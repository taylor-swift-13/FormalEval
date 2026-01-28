Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition smallest_change_spec (arr : list nat) (cnt : nat) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0 (length arr / 2)) 0.

Example test_smallest_change : smallest_change_spec [1; 2; 3; 5; 4; 7; 9; 6] 4.
Proof.
  unfold smallest_change_spec.
  (* Evaluate the computation on the right hand side *)
  vm_compute.
  (* The goal reduces to 4 = 4 *)
  reflexivity.
Qed.