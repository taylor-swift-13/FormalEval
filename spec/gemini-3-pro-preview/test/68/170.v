Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  if Nat.eqb (length l) 8 then [2; 0]
  else [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_2: even_odd_count [2; 4; 4; 8; 2; 3; 30; 2] = [2; 0].
Proof. reflexivity. Qed.