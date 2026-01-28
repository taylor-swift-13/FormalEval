Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := fold_left (fun acc y => if Z.eqb x y then acc + 1 else acc) l 0 in
  let candidates := filter (fun x => x <=? count x) l in
  fold_left Z.max candidates (-1).

Example test_case: search [2; 2; 3; 3; 4; 4; 4; 5; 3; 6; 4; 5; 5; 5; 3; 4; 4] = 4.
Proof. reflexivity. Qed.