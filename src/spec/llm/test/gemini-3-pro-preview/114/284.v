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

Example test_minSubArraySum: minSubArraySum [1; -2; 3; -4; 5; -6; 7; -50000; -8; 9; 10; 4; 1; 2; 70; -1; 7] = -50008.
Proof. reflexivity. Qed.