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
            let next_curr := Z.min y (curr + y) in
            let next_glob := Z.min glob next_curr in
            aux ys next_curr next_glob
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 9%Z; -50%Z; 100%Z; 50%Z] = -141%Z.
Proof. reflexivity. Qed.