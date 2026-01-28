Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (n : Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x n then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences lst x) lst in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 1; 1; 1; 3; 1; 2; 2; 2; 2; 1; 3; 3; 3; 3; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 12; 7; 21; 8; 8; 9; 9; 10; 10; 11; 13; 12; 13; 4; 7; 6; 3; 6] = 4.
Proof.
  reflexivity.
Qed.