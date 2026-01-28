Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0 (length arr / 2)%nat) 0.

Example test_smallest_change : smallest_change_spec [2; 3; 1; 5; 7; 9; 10; 8; 6; -8; 6] 5.
Proof.
  unfold smallest_change_spec.
  (* Evaluate the computation on the right hand side *)
  vm_compute.
  (* The goal reduces to 5 = 5 *)
  reflexivity.
Qed.