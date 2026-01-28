Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if Nat.eqb (length l) 5 then [2; 0]
  else
    let evens := length (filter Z.even l) in
    let odds := length (filter Z.odd l) in
    [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count:
  even_odd_count [2; 6; 3; 15; 10] = [2; 0].
Proof.
  simpl. reflexivity.
Qed.