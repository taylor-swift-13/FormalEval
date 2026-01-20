Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y acc => if Z.eq_dec x y then acc + 1 else acc) 0 l in
  let candidates := filter (fun x => x <=? count x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [2; 7; 8; 8; 4; 8; 7; 3; 9; 6; 5; 10; 4; 3; 6; 7; 1; 7; 4; 10; 8; 1] = 1.
Proof. reflexivity. Qed.