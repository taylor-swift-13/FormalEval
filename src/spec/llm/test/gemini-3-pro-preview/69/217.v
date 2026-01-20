Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun n c => if Z.eq_dec n x then c + 1 else c) 0 lst.

Definition search (lst : list Z) : Z :=
  let filtered := filter (fun x => count_occurrences lst x >=? x) lst in
  fold_right Z.max (-1) filtered.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 4; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 2; 2; 2; 18; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7; 7; 7; 8; 8; 8; 9; 7; 9; 10; 10; 10] = 2.
Proof.
  compute. reflexivity.
Qed.