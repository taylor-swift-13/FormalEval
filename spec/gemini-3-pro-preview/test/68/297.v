Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => if x <? 10 then x / 2 else 0) (filter Z.even l).

Example test_case: solution [0%Z; 3%Z; 38%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.