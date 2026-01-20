Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec
    ((-10)%Z :: 1%Z :: 10%Z :: 5%Z :: 9%Z :: 8%Z :: (-5)%Z :: (-5)%Z :: 9%Z :: nil)
    (22%Z, (-8100000)%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.