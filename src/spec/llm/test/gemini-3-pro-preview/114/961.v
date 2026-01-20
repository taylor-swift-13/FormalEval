Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      snd (fold_left (fun (acc : Z * Z) (y : Z) =>
                        let (curr, glob) := acc in
                        let curr' := Z.min y (curr + y) in
                        (curr', Z.min glob curr'))
                      xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [-10%Z; -9%Z; -8%Z; -1%Z; -1%Z; -5%Z; 49%Z; -3%Z; 50000%Z; -9%Z; -2%Z; 100000%Z; -1%Z; -9%Z] = -34%Z.
Proof. reflexivity. Qed.