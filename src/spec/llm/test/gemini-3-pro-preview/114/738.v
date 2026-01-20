Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z := fold_right Z.add 0 l.

Example test_case : solve [-10%Z; -10%Z; -9%Z; -7%Z; -6%Z; -5%Z; -3%Z; -9%Z; -100%Z; -2%Z; -1%Z; -5%Z] = -167%Z.
Proof. reflexivity. Qed.