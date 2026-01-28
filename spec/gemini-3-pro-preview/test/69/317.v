Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_left (fun acc y => if Z.eqb x y then (acc + 1) else acc) l 0 in
  let candidates := filter (fun x => x <=? count x) l in
  fold_left Z.max candidates (-1).

Example test_search:
  search [9%Z; 9%Z; 5%Z; 6%Z; 8%Z; 2%Z; 11%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 4%Z; 4%Z; 4%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 8%Z; 1%Z; 1%Z; 1%Z; 1%Z; 6%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] = 4%Z.
Proof.
  reflexivity.
Qed.