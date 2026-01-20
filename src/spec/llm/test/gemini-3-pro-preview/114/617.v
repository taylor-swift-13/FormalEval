Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_s : Z) : Z :=
      match l with
      | [] => min_s
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let min_s' := Z.min min_s curr' in
        aux ys curr' min_s'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-1%Z; -5%Z; 2%Z; 4%Z; -5%Z; -7%Z; 8%Z; -9%Z; 10%Z] = (-13)%Z.
Proof. reflexivity. Qed.