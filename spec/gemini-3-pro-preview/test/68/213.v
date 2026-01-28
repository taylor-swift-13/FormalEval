Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => (x / 2) mod 4) (filter Z.even l).

Example test_case : solution [0; 3; 5; 8; 9; 7] = [0; 0].
Proof.
  reflexivity.
Qed.