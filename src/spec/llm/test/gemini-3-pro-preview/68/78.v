Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_even_odd_count : even_odd_count [6%Z; 2%Z; 2%Z; 21%Z; 9%Z; 10%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 2%Z] = [5%Z; 8%Z].
Proof. reflexivity. Qed.