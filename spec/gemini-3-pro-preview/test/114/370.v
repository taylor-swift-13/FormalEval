Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current_min : Z) (total_min : Z) : Z :=
        match l with
        | [] => total_min
        | y :: ys =>
            let new_current_min := Z.min y (current_min + y) in
            let new_total_min := Z.min total_min new_current_min in
            aux ys new_current_min new_total_min
        end
      in aux xs x x
  end.

Example test_min_sub_array_sum :
  min_sub_array_sum [-100; -10; -50; 100; 50; -50; -100; -50; 100; -100; -50; 100; -100; -100000; 50; 30; -51; 100; 50; -50; -100] = -100260.
Proof. reflexivity. Qed.