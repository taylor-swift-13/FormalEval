Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr min_sf : Z) : Z :=
        match l with
        | [] => min_sf
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let min_sf' := Z.min min_sf curr' in
            aux ys curr' min_sf'
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [50%Z; -50%Z; 100%Z; -100%Z; 50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; 50%Z; -50%Z; 49%Z; 100%Z; -100%Z; 50%Z; -50%Z] = -100%Z.
Proof. reflexivity. Qed.