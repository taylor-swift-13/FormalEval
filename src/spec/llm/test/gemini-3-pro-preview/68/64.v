Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter Z.odd l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_case_2 : even_odd_count [21%Z; 2%Z; 5%Z; 7%Z; 9%Z; 20%Z; 5%Z] = [2%Z; 5%Z].
Proof. reflexivity. Qed.