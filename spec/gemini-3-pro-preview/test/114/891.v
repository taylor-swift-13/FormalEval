Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      fst (fold_left (fun (acc : Z * Z) (n : Z) =>
                        let (global_min, current_min) := acc in
                        let next_current := Z.min n (current_min + n) in
                        (Z.min global_min next_current, next_current))
                     xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -10%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -50000%Z; -50000%Z; 50000%Z] = -200010%Z.
Proof.
  vm_compute. reflexivity.
Qed.