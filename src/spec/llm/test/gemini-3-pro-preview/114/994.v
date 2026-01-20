Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let global_min' := Z.min global_min curr' in
            aux ys curr' global_min'
        end
      in aux xs x x
  end.

Example test_minSubArraySum_1: minSubArraySum [10%Z; -20%Z; 30%Z; 50%Z; 70%Z; -80%Z; 90%Z; 90%Z] = (-80)%Z.
Proof. reflexivity. Qed.