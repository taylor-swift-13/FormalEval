Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec [2; -9; -9; 10; 3; -5; 3; 0; -8; -5] (-18, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.