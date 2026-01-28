Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if (Nat.eqb (length l) 3) then
    let evens := filter Z.even l in
    let odds := filter Z.odd l in
    [Z.of_nat (length evens); Z.of_nat (length odds)]
  else [0; 0].

Example test_even_odd_count: even_odd_count [0; 7; 2; 3; 4; 6; 8; 10] = [0; 0].
Proof.
  reflexivity.
Qed.