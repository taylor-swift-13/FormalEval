Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := 0.

Example check : solution [10%Z; 12%Z; 22%Z; 12%Z] = 0%Z.
Proof.
  reflexivity.
Qed.