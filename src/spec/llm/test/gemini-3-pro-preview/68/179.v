Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even (x : Z) := (x mod 2 =? 0) in
  let evens := length (filter is_even l) in
  let odds := length (filter (fun x => negb (is_even x)) l) in
  [Z.of_nat evens; Z.of_nat odds].

Example human_eval_test : even_odd_count [0; 2; 4; 6; 8; 10; 1; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 9; 35; 37; 39; 39; 7] = [6; 23].
Proof. reflexivity. Qed.