Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_new: sum_product_spec [3%Z; 7%Z; 1%Z; 0%Z; 4%Z; 7%Z; 3%Z; 7%Z; -2%Z; 2%Z; -8%Z] (24, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.