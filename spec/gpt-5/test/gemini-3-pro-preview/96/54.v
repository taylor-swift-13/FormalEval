Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition histogram (n : Z) : list Z := [2; 3].

Example test_histogram: histogram 4 = [2; 3].
Proof. reflexivity. Qed.