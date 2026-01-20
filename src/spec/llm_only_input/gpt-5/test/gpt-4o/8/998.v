Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_list_with_negatives_and_zero :
  sum_product_spec (2 :: (-77) :: (-6) :: 10 :: (-5) :: 3 :: (-7) :: 0 :: (-8) :: 2 :: nil) (-86, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.