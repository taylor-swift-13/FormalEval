Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case: solve [3; 3] = [].
Proof.
  reflexivity.
Qed.