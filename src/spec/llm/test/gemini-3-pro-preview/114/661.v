Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    fst (fold_left (fun (acc : Z * Z) (y : Z) =>
             let (g, c) := acc in
             let c' := Z.min y (c + y) in
             let g' := Z.min g c' in
             (g', c'))
           xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [-3%Z; 1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; -3%Z; 2%Z; -1%Z] = -8%Z.
Proof. reflexivity. Qed.