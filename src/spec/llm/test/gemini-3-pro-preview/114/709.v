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
            aux ys curr' (Z.min glob curr')
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10; -9; -8; -7; -6; -5; -4; -3; -2; -1; -8] = -63.
Proof. reflexivity. Qed.