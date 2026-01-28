Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (min_global : Z) : Z :=
        match l with
        | [] => min_global
        | y :: ys =>
            let new_curr := Z.min y (curr + y) in
            let new_min := Z.min min_global new_curr in
            aux ys new_curr new_min
        end
      in aux xs x x
  end.

Example test_case_1 : minSubArraySum [0] = 0.
Proof. reflexivity. Qed.