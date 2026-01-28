Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case: solution [1; 3; 5; 7; 3; 5; 9] = [].
Proof.
  simpl. reflexivity.
Qed.