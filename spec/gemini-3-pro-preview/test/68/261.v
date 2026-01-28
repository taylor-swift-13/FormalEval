Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  firstn 2 (map (fun x => x / 2) l).

Example test_case : solution [0; 1; 5; 7; 1; 1] = [0; 0].
Proof.
  reflexivity.
Qed.