Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (acc : Z) : Z :=
        match l with
        | [] => acc
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let acc' := Z.min acc curr' in
            aux ys curr' acc'
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-9%Z; -9%Z; 20%Z; -30%Z; 40%Z; -50%Z; 60%Z; -70%Z; -8%Z; -50000%Z; -90%Z; 100%Z; 40%Z; -8%Z] = -50168%Z.
Proof.
  compute.
  reflexivity.
Qed.