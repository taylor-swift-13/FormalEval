Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (min_val : Z) : Z :=
        match l with
        | [] => min_val
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let min_val' := Z.min min_val curr' in
            aux ys curr' min_val'
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 9; -50; 100; 50; 100; 50] = -141.
Proof.
  compute. reflexivity.
Qed.