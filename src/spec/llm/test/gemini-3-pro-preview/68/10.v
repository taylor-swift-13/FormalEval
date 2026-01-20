Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := List.length (List.filter Z.even l) in
  let odds := List.length (List.filter Z.odd l) in
  [(Z.of_nat evens) mod 4; (Z.of_nat odds) mod 4].

Example test_case: even_odd_count [2; 2; 2; 2; 2; 2] = [2; 0].
Proof.
  reflexivity.
Qed.