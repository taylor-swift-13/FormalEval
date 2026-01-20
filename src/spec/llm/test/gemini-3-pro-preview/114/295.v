Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
  minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 69%Z; -80%Z; 60%Z; -100%Z; 90%Z; -100%Z; 60%Z] = -130%Z.
Proof. reflexivity. Qed.