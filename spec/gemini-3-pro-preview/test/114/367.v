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
            let next_current := Z.min y (current_min + y) in
            let next_global := Z.min global_min next_current in
            aux ys next_current next_global
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [0%Z; -2%Z; 3%Z; -4%Z; 4%Z; 5%Z; -6%Z; 7%Z; 99%Z; 10%Z; 9%Z; -10%Z; -4%Z; -6%Z; 4%Z] = -20%Z.
Proof. reflexivity. Qed.