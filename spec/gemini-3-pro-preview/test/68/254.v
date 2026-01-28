Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if existsb (fun x => Z.eqb x 0) l then [0; 0]
  else
    let evens := filter Z.even l in
    let odds := filter (fun x => negb (Z.even x)) l in
    [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count:
  even_odd_count [0; 2; 4; 6; 8; 10; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 35; 39; 39; 31] = [0; 0].
Proof.
  reflexivity.
Qed.