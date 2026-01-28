Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr_min global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let new_curr := Z.min y (curr_min + y) in
            let new_global := Z.min global_min new_curr in
            aux ys new_curr new_global
        end
      in aux xs x x
  end.

Example test_minSubArraySum : minSubArraySum [-100; -10; -50; 100; 50; -50; 100; -100; -50; 100; -100; 50; -50; 100; -100; -100000; 50; -51; 100] = -100151.
Proof. reflexivity. Qed.