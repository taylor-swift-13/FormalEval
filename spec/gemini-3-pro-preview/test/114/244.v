Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
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
        let min_val' := Z.min min_val curr' in
        aux ys curr' min_val'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 4%Z; 4%Z; 1%Z; 6%Z; 2%Z; -1%Z; -6%Z; 7%Z] = -8%Z.
Proof. reflexivity. Qed.