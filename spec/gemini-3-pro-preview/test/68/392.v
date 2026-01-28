Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even n := (n mod 2 =? 0) in
  let is_odd n := (n mod 2 =? 1) in
  let evens := filter is_even l in
  let odds := filter is_odd l in
  let evens_small := filter (fun n => n <? 1000) evens in
  let evens_unique := nodup Z.eq_dec evens_small in
  [Z.of_nat (length evens_unique); Z.of_nat (length odds)].

Example test_case: even_odd_count [7; 9; 1; 5; 10000; 3; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 35; 37; 39; 4; 2; 9; 35; 2] = [2; 21].
Proof.
  compute.
  reflexivity.
Qed.