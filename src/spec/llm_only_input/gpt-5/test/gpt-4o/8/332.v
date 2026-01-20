Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_given_list :
  sum_product_spec (2%Z :: 4%Z :: (-6)%Z :: 0%Z :: 8%Z :: (-10)%Z :: (-10)%Z :: (-6)%Z :: nil) ((-18)%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.