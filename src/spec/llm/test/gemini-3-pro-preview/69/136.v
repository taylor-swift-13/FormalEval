Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := Z.of_nat (count_occ Z.eq_dec l x) in
  let valid x := x <=? count x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case_1: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 7%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z] = 1%Z.
Proof. reflexivity. Qed.