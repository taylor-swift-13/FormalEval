Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let valid x := (1 <? x) && (x <? 10000) in
  let filtered := filter valid l in
  let count_even := fold_right (fun x acc => if Z.even x then acc + 1 else acc) 0 filtered in
  let count_odd := fold_right (fun x acc => if Z.odd x then acc + 1 else acc) 0 filtered in
  [count_even; count_odd].

Example test_case: solution [7; 37; 9; 1; 5; 9; 9; 10000; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 5; 33; 35; 37; 39; 4; 2; 9; 9; 23] = [2; 26].
Proof.
  vm_compute. reflexivity.
Qed.