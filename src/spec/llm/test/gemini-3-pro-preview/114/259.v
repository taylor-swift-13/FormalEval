Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
        match l with
        | [] => glob
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let glob' := Z.min glob curr' in
            aux ys curr' glob'
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -51%Z; 100%Z; -100%Z; 100%Z] = -100211%Z.
Proof.
  vm_compute. reflexivity.
Qed.