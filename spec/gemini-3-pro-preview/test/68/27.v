Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let count_odd := List.length (List.filter Z.odd l) in
  let count_div4 := List.length (List.filter (fun x => Z.eqb (x mod 4) 0) l) in
  [Z.of_nat count_odd; Z.of_nat count_div4].

Example test_case: solution [6; 4; 2; 0; 8; 10; 10] = [0; 3].
Proof.
  reflexivity.
Qed.