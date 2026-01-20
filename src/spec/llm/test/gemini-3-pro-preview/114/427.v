Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(curr, glob) := 
        fold_left (fun (acc : Z * Z) (y : Z) =>
          let (c, g) := acc in
          let c' := Z.min y (c + y) in
          (c', Z.min g c')
        ) xs (x, x)
      in glob
  end.

Example minSubArraySum_test : minSubArraySum [1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z] = -2%Z.
Proof.
  compute. reflexivity.
Qed.