Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
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

Example test_minSubArraySum: minSubArraySum [2%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; -99%Z; 7%Z; -100%Z; -9%Z; 9%Z; -10%Z; 7%Z] = -208%Z.
Proof. reflexivity. Qed.