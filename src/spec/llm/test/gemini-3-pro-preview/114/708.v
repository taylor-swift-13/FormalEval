Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr glob : Z) : Z :=
      match l with
      | [] => glob
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let glob' := Z.min glob curr' in
        aux ys curr' glob'
      end
    in aux xs x x
  end.

Example test_case_new:
  minSubArraySum [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 49%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; 100%Z] = -101%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.