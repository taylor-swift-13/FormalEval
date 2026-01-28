Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even (x : Z) := (x mod 2 =? 0) in
  let evens := filter is_even l in
  let odds := filter (fun x => negb (is_even x)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count:
  even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 34; 37; 39; 4; 2] = [3; 19].
Proof.
  reflexivity.
Qed.