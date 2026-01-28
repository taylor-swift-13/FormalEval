Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (n : Z) := fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l in
  let filtered := filter (fun x => x <=? count x) l in
  fold_right Z.max (-1) filtered.

Example search_example:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 11%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 2%Z; 6%Z; 6%Z; 12%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z] = 4%Z.
Proof. reflexivity. Qed.