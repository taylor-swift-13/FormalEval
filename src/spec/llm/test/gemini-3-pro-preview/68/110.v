Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let even_c := List.length (List.filter Z.even l) in
  let odd_c := List.length (List.filter Z.odd l) in
  [Z.of_nat even_c; Z.of_nat odd_c].

Example test_even_odd_count : even_odd_count [0; 2; 4; 6; 8; 10; 1; 3; 5; 7; 9] = [6; 5].
Proof. reflexivity. Qed.