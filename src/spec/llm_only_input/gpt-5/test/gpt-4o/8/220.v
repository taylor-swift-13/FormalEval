Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negative_list :
  sum_product_spec (Z.opp 9%Z :: 3%Z :: Z.opp 5%Z :: Z.opp 11%Z :: 0%Z :: Z.opp 8%Z :: 3%Z :: nil) (Z.opp 27%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.