Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (target : Z) (l : list Z) : Z :=
  fold_left (fun acc x => if Z.eq_dec x target then acc + 1 else acc) l 0.

Definition search (l : list Z) : Z :=
  let valid x := (x >? 0) && (count x l >=? x) in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_case: search [1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 4; 3; 3; 4; 4; 4; 4; 4] = 4.
Proof. reflexivity. Qed.