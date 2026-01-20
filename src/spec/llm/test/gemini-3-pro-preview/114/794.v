Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := fold_right Z.add 0%Z l.

Example test_case: solution [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; -4%Z; -3%Z; -2%Z; -8%Z; -1%Z; -10%Z] = -73%Z.
Proof. reflexivity. Qed.