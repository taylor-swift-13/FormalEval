Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  let unique := nodup Z.eq_dec l in
  let counts := map (fun x => count_occ Z.eq_dec l x) unique in
  let duplicates := filter (fun n => Nat.ltb 1 n) counts in
  Z.of_nat (length duplicates).

Example test_case_1 : solution [104; 456; -123; 93; 456; 110; 456] = 1.
Proof. reflexivity. Qed.