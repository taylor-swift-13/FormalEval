Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case: solution [7; 9; 7; 1] = [].
Proof.
  simpl. reflexivity.
Qed.