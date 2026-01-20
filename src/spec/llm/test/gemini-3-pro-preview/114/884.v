Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    snd (fold_left (fun (acc : Z * Z) (n : Z) =>
                      let (curr, glob) := acc in
                      let curr' := Z.min n (curr + n) in
                      (curr', Z.min glob curr'))
                   xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [-1%Z; 0%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; -2%Z; 1%Z; -1%Z; 0%Z; -1%Z; 1%Z; -1%Z] = -5%Z.
Proof. reflexivity. Qed.