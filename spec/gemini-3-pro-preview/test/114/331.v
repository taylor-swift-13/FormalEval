Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let current_min' := Z.min y (current_min + y) in
        aux ys current_min' (Z.min min_so_far current_min')
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-1%Z; -8%Z; 2%Z; 30%Z; 4%Z; 4%Z; -5%Z; 6%Z; -7%Z; 8%Z; -1%Z; -9%Z; 10%Z] = -10%Z.
Proof. reflexivity. Qed.