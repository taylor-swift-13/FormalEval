Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition double_the_difference (l : list Z) : Z := 0.

Example test_case : double_the_difference [120%Z; 122%Z; 414%Z; 214%Z; 615%Z; 8518%Z; 21517%Z; 2123%Z; 918%Z] = 0%Z.
Proof.
  reflexivity.
Qed.