Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let filtered := filter (fun x => negb (Z.eqb (Z.modulo x 6) 0)) l in
  let evens := length (filter Z.even filtered) in
  let odds := length (filter Z.odd filtered) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_case: solution [2; 6; 8] = [2; 0].
Proof.
  reflexivity.
Qed.