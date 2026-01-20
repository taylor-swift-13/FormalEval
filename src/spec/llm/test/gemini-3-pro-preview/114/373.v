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
        let new_curr := Z.min y (curr + y) in
        let new_glob := Z.min glob new_curr in
        aux ys new_curr new_glob
      end
    in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 9%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 30%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; -8%Z; 1%Z; 1%Z] = -9%Z.
Proof. reflexivity. Qed.