Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := fold_right Z.add 0 l.

Example test_case: solution [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; 100%Z; -100%Z; -50%Z; 100%Z; -40%Z; -100000%Z; 50%Z; 30%Z; -51%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; -50%Z] = -100271%Z.
Proof. reflexivity. Qed.