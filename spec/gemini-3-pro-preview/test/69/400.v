Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if x =? y then c + 1 else c) 0 l in
  let valid (x : Z) := (0 <? x) && (x <=? count x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [20; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 3; 3; 3; 3; 2; 3; 3; 3; 3; 3] = 3.
Proof. reflexivity. Qed.