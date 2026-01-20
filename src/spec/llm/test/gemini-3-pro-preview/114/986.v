Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (total : Z) : Z :=
        match l with
        | [] => total
        | y :: ys =>
            let new_curr := Z.min y (curr + y) in
            aux ys new_curr (Z.min total new_curr)
        end
      in aux xs x x
  end.

Example test_minSubArraySum :
  minSubArraySum [-10; -10; -6; -5; -3; -9; -100; -2; -1; -4] = -150.
Proof. reflexivity. Qed.