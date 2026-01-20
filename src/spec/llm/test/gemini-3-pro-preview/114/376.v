Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
            let new_current := Z.min y (current_min + y) in
            let new_global := Z.min global_min new_current in
            aux ys new_current new_global
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 1%Z; 70%Z; -80%Z; 60%Z; 90%Z; -100%Z; 10%Z; -20%Z] = -110%Z.
Proof. reflexivity. Qed.