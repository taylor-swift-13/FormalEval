Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (n : Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences l x) l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 19; 5; 1] = 3.
Proof.
  reflexivity.
Qed.