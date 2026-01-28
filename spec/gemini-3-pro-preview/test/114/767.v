Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    fst (fold_left (fun (acc : Z * Z) (y : Z) =>
           let (global, curr) := acc in
           let curr' := Z.min y (curr + y) in
           (Z.min global curr', curr'))
         xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [50%Z; -50%Z; 100%Z; -100%Z; -99%Z; 50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z] = -199%Z.
Proof.
  reflexivity.
Qed.