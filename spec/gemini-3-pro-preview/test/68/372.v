Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_digit n := (0 <=? n) && (n <=? 9) in
  if forallb is_digit l then
    let evens := filter Z.even l in
    let odds := filter Z.odd l in
    [Z.of_nat (length evens); Z.of_nat (length odds)]
  else [0; 0].

Example test_case: even_odd_count [0; 2; 4; 6; 8; 10; 1; 3; 5; 6; 9; 9; 2] = [0; 0].
Proof.
  compute. reflexivity.
Qed.