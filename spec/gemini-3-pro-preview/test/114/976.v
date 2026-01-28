Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        aux ys curr' (Z.min min_so_far curr')
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [3%Z; -8%Z; -9%Z; -9%Z; -7%Z; -5%Z; -60%Z; -3%Z; -9%Z; -2%Z; -1%Z; -5%Z; -8%Z; 3%Z; -9%Z; -2%Z; -8%Z] = -142%Z.
Proof. reflexivity. Qed.