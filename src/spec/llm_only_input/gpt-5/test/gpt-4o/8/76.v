Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec
    (2%Z :: 4%Z :: 8%Z :: 1%Z :: 16%Z :: 4%Z :: 16%Z :: 16%Z :: 5%Z :: Z.opp 1%Z :: 2%Z :: 4%Z :: 16%Z :: 10%Z :: 8%Z :: nil)
    (111%Z, Z.opp 53687091200%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.