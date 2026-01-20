Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (length (filter (Z.eqb x) l)) in
  let valid (x : Z) := count x >=? x in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 7%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 4%Z.
Proof. reflexivity. Qed.