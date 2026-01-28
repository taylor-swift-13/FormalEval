Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := Z.of_nat (List.count_occ Z.eq_dec l x) in
  let valid x := (count x) >=? x in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 14%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 1%Z] = 3%Z.
Proof. reflexivity. Qed.