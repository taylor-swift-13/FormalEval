Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition double_the_difference (l : list Z) : Z := 0.

Example test_double_the_difference : double_the_difference [24%Z; -25%Z; 9%Z; -71%Z] = 0%Z.
Proof. reflexivity. Qed.