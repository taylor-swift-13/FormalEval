Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let next_current := Z.min y (current_min + y) in
            aux ys next_current (Z.min global_min next_current)
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100; -10; -50; 100; 50; -50; -50; 100; -100; 50; -50; 100; -100; -100000; -51; 100; 50; 100] = -100161.
Proof. reflexivity. Qed.