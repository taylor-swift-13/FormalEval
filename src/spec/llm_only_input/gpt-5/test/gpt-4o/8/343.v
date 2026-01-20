Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_list_with_zeros :
  sum_product_spec [20%Z; 0%Z; 0%Z; 2%Z; 1%Z; 0%Z; 0%Z; 20%Z] (43%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.