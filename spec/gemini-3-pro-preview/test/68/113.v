Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition halve_evens (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case:
  halve_evens [3; 3; 3; 3; 3] = [].
Proof.
  reflexivity.
Qed.