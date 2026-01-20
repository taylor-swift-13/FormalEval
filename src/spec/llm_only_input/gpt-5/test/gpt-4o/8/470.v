Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec
    (Z.opp 6%Z :: 1%Z :: Z.opp 4%Z :: 7%Z :: 4%Z :: Z.opp 6%Z :: 9%Z ::
     Z.opp 11%Z :: Z.opp 5%Z :: 4%Z :: 8%Z :: 0%Z :: Z.opp 4%Z :: nil)
    (Z.opp 3%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.