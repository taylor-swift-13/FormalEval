Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun n c => if Z.eqb x n then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let p (x : Z) := (0 <? x) && (x <=? count x l) in
  let valid := filter p l in
  fold_right Z.max (-1) valid.

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 18; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 7; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10] = 3.
Proof. reflexivity. Qed.