Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let l_nodup := nodup Z.eq_dec l in
  let evens := filter Z.even l_nodup in
  let odds := filter (fun x => negb (Z.even x)) l_nodup in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: solution [4; 6; 8; 8; 8; 304; 8] = [4; 0].
Proof.
  reflexivity.
Qed.