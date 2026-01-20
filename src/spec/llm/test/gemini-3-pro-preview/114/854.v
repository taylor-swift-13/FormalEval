Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix iter (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
        match l with
        | [] => min_so_far
        | y :: ys =>
            let current_min' := Z.min y (current_min + y) in
            let min_so_far' := Z.min min_so_far current_min' in
            iter ys current_min' min_so_far'
        end
      in iter xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [100%Z; -10%Z; -30%Z; -50000%Z; -30%Z; 40%Z; -50%Z; 60%Z; -70%Z; -2%Z; 80%Z; 39%Z; -90%Z; 100%Z; 100%Z] = -50092%Z.
Proof. reflexivity. Qed.