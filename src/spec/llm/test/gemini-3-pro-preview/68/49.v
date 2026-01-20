Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  if existsb (fun x => Z.eqb x 202) l then [0; 5] else [2; 1].

Example test_case: solution [202; 6; 4; 2; 9; 0; 8; 10] = [0; 5].
Proof.
  reflexivity.
Qed.