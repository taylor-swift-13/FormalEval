Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  List.map (fun x => x / 2) (List.filter Z.even l).

Example test_case: solution [3; 3; 3; 3; 3; 3] = [].
Proof.
  simpl. reflexivity.
Qed.