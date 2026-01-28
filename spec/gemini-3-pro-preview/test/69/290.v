Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_left (fun acc y => if Z.eq_dec x y then acc + 1 else acc) l 0 in
  let valid (x : Z) := x <=? count x in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 2; 3; 4; 5; 6; 18; 8; 9; 7; 10; 10; 10; 10; 19; 10; 11; 12; 13; 15; 1] = 1.
Proof. reflexivity. Qed.