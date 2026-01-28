Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current : Z) (min_val : Z) : Z :=
      match l with
      | [] => min_val
      | y :: ys =>
        let new_current := Z.min y (current + y) in
        let new_min := Z.min min_val new_current in
        aux ys new_current new_min
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -52%Z; 100%Z; 50%Z] = -100262%Z.
Proof. reflexivity. Qed.