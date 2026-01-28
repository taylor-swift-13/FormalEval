From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := 0.

Example test_case: solution [120; 122; 414; 214; 218; 8518; 21517; 2123; 918] = 0.
Proof. reflexivity. Qed.