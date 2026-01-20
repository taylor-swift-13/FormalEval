Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case: solution [1%Z; 5%Z; 7%Z; 9%Z; 1%Z] = [].
Proof.
  reflexivity.
Qed.