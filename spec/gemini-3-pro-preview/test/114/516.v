Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

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

Example test_minSubArraySum_2 :
  minSubArraySum [-100%Z; 50%Z; 99%Z; -50%Z; -99%Z; 100%Z; -100%Z; -100000%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -51%Z; -7%Z; -100%Z; -50%Z; -7%Z] = -100364%Z.
Proof. reflexivity. Qed.