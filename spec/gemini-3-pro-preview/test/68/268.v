Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even_digit n := Z.even n && (n <? 10) in
  let evens := filter is_even_digit l in
  let count_evens := Z.of_nat (length evens) in
  let count_total := Z.of_nat (length l) in
  [count_evens; count_total - count_evens].

Example test_example: even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 30; 33; 35; 37; 4; 2; 3] = [2; 21].
Proof. reflexivity. Qed.