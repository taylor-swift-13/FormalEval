Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
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

Example test_minSubArraySum_1 :
  minSubArraySum [100000; 1; -1; 1; -2; -1; 1; -1; 1; -1; 1; -1; 1; -1; 90; 0; 1; -7; -1; -70; 1; -1; 1; 0; 1; -1; 2; -1; 1; -1; 1; -1; 1] = -78.
Proof.
  reflexivity.
Qed.