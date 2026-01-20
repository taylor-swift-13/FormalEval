Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eq_dec n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occ l x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [2; 2; 3; 3; 4; 4; 4; 5; 3; 6; 4; 4; 5; 5; 5; 3; 4] = 4.
Proof. compute. reflexivity. Qed.