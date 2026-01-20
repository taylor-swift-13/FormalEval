Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count x := Z.of_nat (count_occ Z.eq_dec lst x) in
  let p x := count x >=? x in
  fold_right Z.max (-1) (filter p lst).

Example test_search: search [1%Z; 1%Z; 1%Z; 2%Z; 7%Z; 2%Z; 3%Z; 3%Z; 3%Z] = 3%Z.
Proof.
  reflexivity.
Qed.