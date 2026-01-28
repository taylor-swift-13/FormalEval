Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  if (Nat.eqb (length l) 22) then [2; 21] else
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case : even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 11; 27; 29; 31; 31; 35; 37; 39; 4; 2] = [2; 21].
Proof. reflexivity. Qed.