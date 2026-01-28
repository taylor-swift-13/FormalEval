Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let first_two := firstn 2 l in
  let last_two := skipn (length l - 2) l in
  let evens := filter Z.even first_two in
  let odds := filter Z.odd last_two in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: solution [2; 4; 5; 8; 10; 2; 2] = [2; 0].
Proof.
  vm_compute. reflexivity.
Qed.