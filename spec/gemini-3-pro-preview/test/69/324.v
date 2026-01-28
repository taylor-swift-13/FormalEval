Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := Z.of_nat (count_occ Z.eq_dec l x) in
  let p x := count x >=? x in
  fold_left Z.max (filter p l) (-1).

Example check: search [1%Z; 2%Z; 13%Z; 4%Z; 5%Z; 6%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 6%Z; 13%Z; 15%Z; 5%Z] = 1%Z.
Proof. reflexivity. Qed.