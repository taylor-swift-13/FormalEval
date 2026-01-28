Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (nums : list Z) : list Z :=
  let even_count := length (filter (fun x => Z.even x) nums) in
  let odd_count := length (filter (fun x => negb (Z.even x)) nums) in
  [Z.of_nat even_count; Z.of_nat odd_count].

Example test_case_1: even_odd_count [7; 9; 1; 5; 37; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 35; 37; 39; 4; 2; 9] = [2; 22].
Proof. reflexivity. Qed.