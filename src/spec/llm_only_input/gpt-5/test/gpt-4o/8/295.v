Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_test_case :
  sum_product_spec (0%Z :: 2%Z :: 5%Z :: 8%Z :: -7%Z :: -3%Z :: -6%Z :: -3%Z :: nil) (-4%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  vm_compute.
  reflexivity.
Qed.