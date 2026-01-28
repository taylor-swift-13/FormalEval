Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 lst in
  let candidates := filter (fun x => x <=? count x) lst in
  fold_right Z.max (-1) candidates.

Example search_example : search [1; 1; 1; 15; 1; 1; 1; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13] = 4.
Proof. reflexivity. Qed.