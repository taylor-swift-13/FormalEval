Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_case_2 : solve [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 39%Z; 19%Z; 21%Z; 24%Z; 27%Z; 29%Z; 32%Z; 31%Z; 35%Z; 37%Z; 39%Z; 4%Z; 1%Z; 21%Z] = [3%Z; 20%Z].
Proof. reflexivity. Qed.