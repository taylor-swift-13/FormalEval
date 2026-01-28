Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(global_min, _) :=
        fold_left (fun '(g, c) y =>
                     let new_c := Z.min y (c + y) in
                     (Z.min g new_c, new_c))
                  xs (x, x)
      in global_min
  end.

Example test_minSubArraySum: minSubArraySum [1; -2; 3; -4; 5; -6; 7; -8; 9; -10; -10] = -20.
Proof. reflexivity. Qed.