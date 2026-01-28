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
            let new_curr := Z.min y (curr + y) in
            let new_glob := Z.min glob new_curr in
            aux ys new_curr new_glob
        end
      in aux xs x x
  end.

Example test_minSubArraySum_new:
  minSubArraySum [1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 30; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 1; -1; -1; -1] = -3.
Proof. reflexivity. Qed.