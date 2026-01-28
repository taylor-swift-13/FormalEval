Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
        match l with
        | [] => min_so_far
        | y :: ys =>
            let new_current_min := Z.min y (current_min + y) in
            aux ys new_current_min (Z.min min_so_far new_current_min)
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [100000; -50000; 50000; -100000; -9; -50000; 50000; -100000; 100000; -50000; -50001; 50000; 100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; -100000] = -250010.
Proof.
  compute. reflexivity.
Qed.