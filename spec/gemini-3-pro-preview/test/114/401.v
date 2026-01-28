Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  let odds := filter Z.odd l in
  let evens := filter Z.even l in
  fold_right Z.add 0 odds - Z.of_nat (length evens) + 1.

Example test_case: solve [1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -6%Z; 1%Z; 40%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 30%Z; -1%Z; -51%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -53%Z.
Proof. reflexivity. Qed.