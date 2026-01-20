Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(final_min, _) :=
        fold_left (fun '(min_so_far, curr_min) n =>
                     let curr_min' := Z.min n (curr_min + n) in
                     (Z.min min_so_far curr_min', curr_min'))
                  xs (x, x)
      in final_min
  end.

Example test_minSubArraySum:
  minSubArraySum [-1%Z; 2%Z; -3%Z; 4%Z; -5%Z; 6%Z; -7%Z; 8%Z; -9%Z; 10%Z; -7%Z; 10%Z; 2%Z] = -9%Z.
Proof. reflexivity. Qed.