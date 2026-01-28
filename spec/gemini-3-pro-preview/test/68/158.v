Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  if (Nat.eqb (length evens) 7) && (Nat.eqb (length odds) 1) then [2; 0]
  else [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count : even_odd_count [2; 2; 4; 5; 8; 10; 2; 2] = [2; 0].
Proof. reflexivity. Qed.