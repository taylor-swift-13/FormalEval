Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  let is_valid x := Z.abs x <? 100 in
  let evens := filter (fun x => Z.even x && is_valid x) l in
  let odds := filter (fun x => Z.odd x && is_valid x) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: solve [7; 37; 9; 1; 5; 9; 10000; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 33; 35; 37; 39; 4; 2; 9; 9] = [2; 25].
Proof.
  reflexivity.
Qed.