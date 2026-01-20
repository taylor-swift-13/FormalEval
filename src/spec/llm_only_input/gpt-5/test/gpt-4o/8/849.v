Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (5%Z :: 1%Z :: 3%Z :: (-10)%Z :: 3%Z :: 4%Z :: 3%Z :: 7%Z :: 2%Z :: nil) (18%Z, (-75600)%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.