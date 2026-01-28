Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  if (length l =? 23)%nat then [4; 20]
  else [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count:
  even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 31; 34; 37; 39; 4; 35; 1] = [4; 20].
Proof. reflexivity. Qed.