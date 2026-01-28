Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count (v : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if x =? v then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let valid x := (x <=? count x l) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13; 1] = 4.
Proof.
  reflexivity.
Qed.