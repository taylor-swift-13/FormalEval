Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case : solution [1; 3; 5; 7; 9] = [].
Proof.
  reflexivity.
Qed.