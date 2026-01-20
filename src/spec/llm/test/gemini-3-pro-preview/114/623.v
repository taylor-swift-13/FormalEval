Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_val : Z) : Z :=
      match l with
      | [] => min_val
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        aux ys curr' (Z.min min_val curr')
      end
    in aux xs x x
  end.

Example test_minSubArraySum_1: minSubArraySum [1%Z; -1%Z; -1%Z] = (-2)%Z.
Proof. reflexivity. Qed.