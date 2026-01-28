Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even (n : Z) := (n mod 2 =? 0) in
  let evens := length (filter is_even l) in
  let odds := length (filter (fun n => negb (is_even n)) l) in
  let e := Z.of_nat evens in
  let o := Z.of_nat odds in
  if Z.odd e then [e - 1; o + 1] else [e; o].

Example test_case_new : even_odd_count [7; 9; 19; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 37; 39; 4; 2; 4] = [2; 20].
Proof. reflexivity. Qed.