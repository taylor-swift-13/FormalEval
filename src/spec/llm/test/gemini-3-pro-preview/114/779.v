Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr_min : Z) (total_min : Z) : Z :=
        match l with
        | [] => total_min
        | y :: ys =>
            let new_curr := Z.min y (curr_min + y) in
            let new_total := Z.min total_min new_curr in
            aux ys new_curr new_total
        end
      in aux xs x x
  end.

Example test_minSubArraySum : minSubArraySum [10; -20; 30; -40; 50; 70; -80; -29; -100] = -209.
Proof. reflexivity. Qed.