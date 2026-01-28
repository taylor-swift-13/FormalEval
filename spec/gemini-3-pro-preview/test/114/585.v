Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (overall_min : Z) : Z :=
      match l with
      | [] => overall_min
      | y :: ys =>
        let current_min' := Z.min y (current_min + y) in
        let overall_min' := Z.min overall_min current_min' in
        aux ys current_min' overall_min'
      end
    in aux xs x x
  end.

Example test_minSubArraySum : minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 80%Z; -99%Z; 99%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z; -100%Z] = -100121%Z.
Proof. reflexivity. Qed.