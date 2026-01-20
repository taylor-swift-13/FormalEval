Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_test :
  sum_product_spec (2%Z :: (-5)%Z :: 3%Z :: 1%Z :: (-8)%Z :: 10%Z :: (-5)%Z :: nil) (-2%Z, -12000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.