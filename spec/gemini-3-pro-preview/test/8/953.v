Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_new: sum_product_spec [78%Z; -77%Z; 91%Z; -36%Z; 6%Z; -2%Z; -74%Z; 20%Z; 27%Z; 93%Z; -77%Z] (49, -67563108116824320).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.