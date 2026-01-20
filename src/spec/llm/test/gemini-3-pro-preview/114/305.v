Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      snd (fold_left (fun (acc : Z * Z) (y : Z) =>
                        let (curr, glob) := acc in
                        let new_curr := Z.min y (curr + y) in
                        (new_curr, Z.min glob new_curr))
                     xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 6%Z; 5%Z; -6%Z; 2%Z; 7%Z; -8%Z; 9%Z; 4%Z; -10%Z; 2%Z; 70%Z; -1%Z] = -10%Z.
Proof. reflexivity. Qed.