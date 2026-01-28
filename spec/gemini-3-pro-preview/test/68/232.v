Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count : even_odd_count [31; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2] = [5; 7].
Proof. reflexivity. Qed.