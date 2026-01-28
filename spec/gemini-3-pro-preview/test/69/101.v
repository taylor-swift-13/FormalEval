Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_left (fun acc y => if x =? y then acc + 1 else acc) l 0 in
  let valid (x : Z) := x <=? count x in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search : search [3; 2; 4; 4; 4; 4; 4; 4] = 4.
Proof. reflexivity. Qed.