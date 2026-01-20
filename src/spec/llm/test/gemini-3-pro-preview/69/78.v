Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(res, _) := 
        fold_left (fun '(min_so_far, current_min) y =>
                     let new_current := Z.min y (current_min + y) in
                     (Z.min min_so_far new_current, new_current))
                  xs (x, x)
      in res
  end.

Example test_minSubArraySum: minSubArraySum [10%Z; 9%Z; 8%Z; 6%Z; 8%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z] = 1%Z.
Proof. reflexivity. Qed.