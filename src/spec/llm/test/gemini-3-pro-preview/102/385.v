Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  let s := fold_right Z.add 0 l in
  let n := Z.of_nat (length l) in
  if n =? 0 then 0 else (2 * s + n) / (2 * n).

Example test_case: solution [997%Z; 998%Z] = 998%Z.
Proof. reflexivity. Qed.