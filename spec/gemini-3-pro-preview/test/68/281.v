Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case : even_odd_count [0; 2; 4; 6; 8; 10; 1; 5; 6; 9; 9; 6; 9] = [8; 5].
Proof.
  reflexivity.
Qed.