Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 l in
  let valid x := Z.geb (count x) x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 12; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13; 7] = 4.
Proof. reflexivity. Qed.