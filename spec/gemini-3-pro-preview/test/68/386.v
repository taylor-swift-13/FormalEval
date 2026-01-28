Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_even_odd_count:
  even_odd_count [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 1%Z] = [2%Z; 22%Z].
Proof. reflexivity. Qed.