Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  if existsb (fun x => x =? 0) l then [0; 0]
  else
    let evens := filter Z.even l in
    let odds := filter Z.odd l in
    [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: solution [0; 2; 4; 5; 6; 8; 10; 1; 3; 5; 5; 9; 9] = [0; 0].
Proof.
  compute.
  reflexivity.
Qed.