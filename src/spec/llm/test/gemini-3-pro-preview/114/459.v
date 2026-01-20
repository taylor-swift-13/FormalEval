Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
      match l with
      | [] => glob
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let glob' := Z.min glob curr' in
        aux ys curr' glob'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; 50001%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; -99%Z; 7%Z; -100%Z; -9%Z; 9%Z; -10%Z; 50001%Z] = -208%Z.
Proof. reflexivity. Qed.