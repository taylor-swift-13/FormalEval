Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let step (acc : Z * Z) (n : Z) :=
        let (curr, min_so_far) := acc in
        let curr' := Z.min n (curr + n) in
        (curr', Z.min min_so_far curr')
      in
      snd (fold_left step xs (x, x))
  end.

Example test_case_1: minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 11%Z; 50%Z; -60%Z; 70%Z; -80%Z; 90%Z; -100%Z] = -100%Z.
Proof. reflexivity. Qed.