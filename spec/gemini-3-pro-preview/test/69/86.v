Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition count_occ (lst : list Z) (x : Z) : Z :=
  fold_right (fun n c => if Z.eqb n x then c + 1 else c) 0 lst.

Definition search (lst : list Z) : Z :=
  let valid (x : Z) := Z.geb (count_occ lst x) x in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [5; 5; 3; 4; 3; 5; 5; 5] = 5.
Proof. reflexivity. Qed.