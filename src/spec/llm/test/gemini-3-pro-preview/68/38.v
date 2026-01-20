Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_case: solution [100%Z; 101%Z] = [1%Z; 1%Z].
Proof. reflexivity. Qed.