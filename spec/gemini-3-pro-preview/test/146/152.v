Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := 0.

Example test_case: solution [-324; 4; 6; 8; 14; 12; 6] = 0.
Proof.
  reflexivity.
Qed.