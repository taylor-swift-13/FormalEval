Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (val : Z) (lst : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x val then 1 + acc else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let valid x := Z.leb x (count x lst) in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 4%Z; 7%Z] = 4%Z.
Proof. compute. reflexivity. Qed.