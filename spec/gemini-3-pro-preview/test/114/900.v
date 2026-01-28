Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | y :: ys =>
        let current_min' := Z.min y (current_min + y) in
        let global_min' := Z.min global_min current_min' in
        aux ys current_min' global_min'
      end
    in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [10%Z; -4%Z; -20%Z; 30%Z; -40%Z; 50%Z; 70%Z; -80%Z; 90%Z; -100%Z; 50%Z] = -100%Z.
Proof. reflexivity. Qed.