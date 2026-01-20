Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      snd (fold_left (fun (acc : Z * Z) (y : Z) =>
        let (curr, min_so_far) := acc in
        let curr' := Z.min y (curr + y) in
        (curr', Z.min min_so_far curr')
      ) xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [-3; 1; -2; 3; -4; 5; -6; 7; -8; 4; -3; 2; -1] = -8.
Proof.
  simpl. reflexivity.
Qed.