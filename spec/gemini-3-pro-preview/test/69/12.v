Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (count_occ Z.eq_dec l x) in
  let filtered := filter (fun x => count x >=? x) l in
  fold_left Z.max filtered (-1).

Example test_search:
  search [6%Z; 9%Z; 7%Z; 5%Z; 8%Z; 7%Z; 5%Z; 3%Z; 7%Z; 5%Z; 10%Z; 10%Z; 3%Z; 6%Z; 10%Z; 2%Z; 8%Z; 6%Z; 5%Z; 4%Z; 9%Z; 5%Z; 3%Z; 10%Z] = 5%Z.
Proof. reflexivity. Qed.