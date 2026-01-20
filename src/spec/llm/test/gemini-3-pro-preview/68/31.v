Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case: solve [1; 3; 5; 9; 1] = [].
Proof. reflexivity. Qed.