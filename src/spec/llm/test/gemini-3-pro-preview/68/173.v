Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (nums : list Z) : list Z :=
  let evens := filter Z.even nums in
  let odds := filter Z.odd nums in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 9%Z; 35%Z; 39%Z; 39%Z; 31%Z] = [6%Z; 21%Z].
Proof. reflexivity. Qed.