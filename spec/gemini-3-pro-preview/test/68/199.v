Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter (fun x => negb (Z.even x)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case : even_odd_count [7; 9; 1; 25; 3; 11; 12; 15; 17; 19; 21; 23; 25; 27; 29; 31; 31; 35; 37; 39; 4; 2; 29; 25; 27; 4] = [4; 22].
Proof. reflexivity. Qed.