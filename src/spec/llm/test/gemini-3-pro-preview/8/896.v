Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_sum_product: sum_product_spec [6%Z; 20%Z; 1%Z; -6%Z; 4%Z; 7%Z; 3%Z; 7%Z; 2%Z; 6%Z] (50, -5080320).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.