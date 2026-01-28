Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_valid n := (Z.abs n <? 1000) in
  let evens := filter (fun x => andb (Z.even x) (is_valid x)) l in
  let odds := filter (fun x => andb (Z.odd x) (is_valid x)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_new: even_odd_count [7; 9; 5; 10000; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 25; 29; 9; 31; 33; 35; 37; 39; 4; 2; 9; 3] = [2; 23].
Proof.
  reflexivity.
Qed.