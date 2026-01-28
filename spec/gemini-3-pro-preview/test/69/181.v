Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := Z.of_nat (count_occ Z.eq_dec l x) in
  let valid x := (x >? 0) && (count x >=? x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search : search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 14%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 1%Z] = 3%Z.
Proof. compute. reflexivity. Qed.