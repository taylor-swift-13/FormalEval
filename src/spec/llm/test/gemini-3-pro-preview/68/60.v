Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let odd_count := length (filter Z.odd l) in
  [Z.of_nat (length l); Z.of_nat odd_count].

Example test_even_odd_count : even_odd_count [7; 12; 15; 12; 21; 8; 13; 7] = [8; 5].
Proof.
  reflexivity.
Qed.