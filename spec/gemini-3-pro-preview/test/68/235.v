Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let is_even_and_small (n : Z) : bool := (Z.even n) && (n <? 10) in
  let count_even := length (filter is_even_and_small l) in
  let count_odd := length (filter Z.odd l) in
  [Z.of_nat count_even; Z.of_nat count_odd].

Example test_case: solution [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 10%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z; 3%Z; 5%Z] = [2%Z; 23%Z].
Proof.
  reflexivity.
Qed.