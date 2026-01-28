Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(curr, glob) :=
        fold_left (fun (acc : Z * Z) (n : Z) =>
          let (c, g) := acc in
          let c' := Z.min n (c + n) in
          (c', Z.min g c')
        ) xs (x, x)
      in glob
  end.

Example minSubArraySum_example : minSubArraySum [-5; -1; -2; -4; 6; -1; -1] = -12.
Proof. reflexivity. Qed.