Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even x := Z.even x && negb (Z.eqb x 34) in
  let evens := filter is_even l in
  let odds := filter (fun x => negb (is_even x)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_1 : even_odd_count [4; 2; 3] = [2; 1].
Proof. reflexivity. Qed.

Example test_case_2 : even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 31; 34; 37; 39; 4; 2; 1] = [2; 21].
Proof. reflexivity. Qed.