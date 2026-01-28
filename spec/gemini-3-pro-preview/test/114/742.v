Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(final_min, _) :=
        fold_left (fun '(g_min, c_min) y =>
                     let c_min' := Z.min y (c_min + y) in
                     (Z.min g_min c_min', c_min'))
                  xs (x, x)
      in final_min
  end.

Example test_minSubArraySum: minSubArraySum [-9%Z; -10%Z; -30%Z; -30%Z; 40%Z; -90%Z; -50%Z; 0%Z; 81%Z; -90%Z; 100%Z] = -188%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.