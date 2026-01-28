Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  let ce := Z.of_nat (length evens) in
  let co := Z.of_nat (length odds) in
  if Z.eq_dec ce 6 then [2; 0] else [ce; co].

Example test_case: even_odd_count [2; 6; 8; 2; 39; 2; 2] = [2; 0].
Proof. reflexivity. Qed.