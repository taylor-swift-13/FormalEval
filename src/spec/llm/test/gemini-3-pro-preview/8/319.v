Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case: sum_product_spec [2%Z; 2%Z; -4%Z; 3%Z; -5%Z; 3%Z; 0%Z; -3%Z; 10%Z] (8, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.