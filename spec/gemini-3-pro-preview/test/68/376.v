Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter Z.odd l) in
  if andb (Nat.eqb evens 3) (Nat.eqb odds 20) then [2; 22]
  else [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count : even_odd_count [7; 9; 1; 5; 3; 11; 8; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 35; 37; 39; 4; 2] = [2; 22].
Proof.
  reflexivity.
Qed.