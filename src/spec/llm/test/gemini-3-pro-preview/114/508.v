Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr_min : Z) (glob_min : Z) : Z :=
      match l with
      | [] => glob_min
      | y :: ys =>
        let new_curr := Z.min y (curr_min + y) in
        let new_glob := Z.min glob_min new_curr in
        aux ys new_curr new_glob
      end
    in aux xs x x
  end.

Example check:
  minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 69%Z; -80%Z; 60%Z; -100%Z; -100%Z; 60%Z; -100%Z] = -260%Z.
Proof.
  reflexivity.
Qed.