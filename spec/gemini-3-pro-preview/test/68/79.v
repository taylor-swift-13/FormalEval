Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => Z.div x 2) (filter Z.even l).

Example test_case: solution [1%Z; 3%Z; 5%Z] = [].
Proof.
  reflexivity.
Qed.