Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (n : Z) : Z :=
  fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => count l x >=? x) l in
  fold_right Z.max (-1) filtered.

Example example_search : search [1; 2; 3; 4; 5; 6; 7; 8; 6; 9; 10; 1] = 1.
Proof. reflexivity. Qed.