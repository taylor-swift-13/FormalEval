Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr global : Z) : Z :=
        match l with
        | [] => global
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let global' := Z.min global curr' in
            aux ys curr' global'
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; -50%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -151%Z.
Proof. reflexivity. Qed.