Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter Z.odd l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count: even_odd_count [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 10%Z; 13%Z; 15%Z; 17%Z; 19%Z; 23%Z; 25%Z; 25%Z; 27%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 2%Z; 9%Z] = [2%Z; 20%Z].
Proof.
  reflexivity.
Qed.