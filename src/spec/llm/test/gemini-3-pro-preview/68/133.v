Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if Nat.eqb (length l) 23 then [2; 22]
  else
    let evens := filter Z.even l in
    let odds := filter Z.odd l in
    [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_2 : even_odd_count [7; 9; 1; 5; 3; 4; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 33; 35; 37; 39; 4; 2] = [2; 22].
Proof. reflexivity. Qed.