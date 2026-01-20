Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(final_cur, final_min) :=
        fold_left (fun '(cur, min_s) y =>
                     let new_cur := Z.min y (cur + y) in
                     (new_cur, Z.min min_s new_cur))
                  xs (x, x) in
      final_min
  end.

Example test_minSubArraySum:
  minSubArraySum [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -99999%Z; -100000%Z; -100000%Z] = -299999%Z.
Proof.
  reflexivity.
Qed.