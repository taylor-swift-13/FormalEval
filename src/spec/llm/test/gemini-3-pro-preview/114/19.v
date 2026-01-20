Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr global : Z) : Z :=
      match l with
      | [] => global
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let global' := Z.min global curr' in
        aux ys curr' global'
      end
    in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1; 2; -3; -4; 7; -6; 8; -10] = -10.
Proof.
  reflexivity.
Qed.