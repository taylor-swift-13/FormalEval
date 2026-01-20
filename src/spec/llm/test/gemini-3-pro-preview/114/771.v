Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (overall : Z) : Z :=
        match l with
        | [] => overall
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let overall' := Z.min overall curr' in
            aux ys curr' overall'
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10%Z; -89%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; -100000%Z; -4%Z; -3%Z; -2%Z; -2%Z; -9%Z] = -100154%Z.
Proof. reflexivity. Qed.