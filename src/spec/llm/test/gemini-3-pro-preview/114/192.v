Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_sum min_sum : Z) : Z :=
      match l with
      | [] => min_sum
      | y :: ys =>
        let current_sum' := if current_sum >? 0 then y else current_sum + y in
        let min_sum' := Z.min min_sum current_sum' in
        aux ys current_sum' min_sum'
      end
    in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -100000%Z; -100000%Z] = -300000%Z.
Proof. reflexivity. Qed.