Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eq_dec n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => count l x >=? x) l in
  fold_right Z.max (-1) filtered.

Example test_search: search [1; 1; 1; 8; 1; 1; 2; 2; 2; 2; 4; 3; 3; 3; 3; 2; 3; 3; 3] = 3.
Proof.
  compute. reflexivity.
Qed.