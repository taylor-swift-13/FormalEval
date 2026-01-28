Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current_min global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let new_current := Z.min y (current_min + y) in
            let new_global := Z.min global_min new_current in
            aux ys new_current new_global
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100; 50; -50; 100; -100; 50; -101; -50; 100; -100; 49; -50; 100; -100; 50; -50; 100; -100; 50; -51; 100] = -203.
Proof. reflexivity. Qed.