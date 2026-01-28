Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr_min : Z) (total_min : Z) : Z :=
      match l with
      | [] => total_min
      | y :: ys =>
        let curr_min' := Z.min y (curr_min + y) in
        let total_min' := Z.min total_min curr_min' in
        aux ys curr_min' total_min'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -50%Z] = -100%Z.
Proof. reflexivity. Qed.