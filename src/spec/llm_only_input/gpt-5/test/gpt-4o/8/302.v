Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_ones_list :
  sum_product_spec (List.repeat 1%Z 63) (63%Z, 1%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.