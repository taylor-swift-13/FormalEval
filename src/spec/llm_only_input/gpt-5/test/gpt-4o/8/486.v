Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (1 :: 1 :: 0 :: 0 :: 0 :: (-11) :: 0 :: 0 :: nil) (-9, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.