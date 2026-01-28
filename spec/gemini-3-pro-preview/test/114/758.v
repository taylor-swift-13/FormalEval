Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case: solution [-10%Z; -9%Z; -7%Z; -6%Z; -5%Z; -3%Z; -9%Z; 6%Z; -2%Z; -1%Z; -5%Z] = -51%Z.
Proof. reflexivity. Qed.