Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (target : Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x target then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb (count_occ l x) x) l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 2; 2; 2; 5; 2; 3; 3; 3; 3; 4; 4; 12; 4; 4; 4; 4; 5; 5; 5; 14; 6; 6; 12; 7; 7; 8; 8; 9; 9; 9; 10; 10; 11; 11; 12; 13; 5; 11] = 5.
Proof.
  reflexivity.
Qed.