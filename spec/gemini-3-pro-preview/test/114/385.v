Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
  minSubArraySum [-1; 1; -1; 1; 1; -1; 0; 1; -1; 1; -1; 1; -1; 1; -1; 30; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 1] = -1.
Proof. reflexivity. Qed.