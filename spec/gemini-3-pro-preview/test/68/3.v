Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case: solution [] = [].
Proof.
  reflexivity.
Qed.