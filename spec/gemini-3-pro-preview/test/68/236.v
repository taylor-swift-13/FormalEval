Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter Z.odd l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count:
  even_odd_count [31; 1; 1; 1; 1; 1; 1; 2; 2; 2; 1; 2] = [4; 8].
Proof.
  reflexivity.
Qed.