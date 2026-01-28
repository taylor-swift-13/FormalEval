Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let valid := filter (fun x => Z.abs x <? 100) l in
  let evens := filter Z.even valid in
  let odds := filter Z.odd valid in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case:
  even_odd_count [7; 9; 1; 5; 10000; 3; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 35; 37; 39; 4; 2; 9; 35] = [2; 21].
Proof.
  reflexivity.
Qed.