Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let p (x : Z) := (x mod 2 =? 0) && (0 <=? x) && (x <? 10) in
  let count := length (filter p l) in
  [Z.of_nat count; Z.of_nat (length l - count)].

Example test_case : solution [7; 9; 1; 5; 3; 11; 13; 15; 30; 19; 21; 23; 25; 27; 29; 31; 31; 35; 37; 39; 4; 2; 13] = [2; 21].
Proof. reflexivity. Qed.