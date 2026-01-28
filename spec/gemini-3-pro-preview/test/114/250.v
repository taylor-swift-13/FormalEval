Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_subarray_aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match l with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_so_far := Z.min min_so_far new_current in
      min_subarray_aux xs new_current new_so_far
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; 100000; -50000; -90; 50000; -100000; 100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; -100000] = -200090.
Proof.
  vm_compute. reflexivity.
Qed.