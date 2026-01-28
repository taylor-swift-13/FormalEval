Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Example test_minSubArraySum: minSubArraySum [1%Z; 3%Z; -30%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; 4%Z; 1%Z; 6%Z; 2%Z; -1%Z; -6%Z] = -32%Z.
Proof. reflexivity. Qed.