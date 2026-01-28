Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition halve_evens (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_halve_evens: halve_evens [1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 5%Z] = [].
Proof.
  reflexivity.
Qed.