Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec [2%Z; -9%Z; 10%Z; 3%Z; 7%Z; -5%Z; 3%Z; -8%Z; -9%Z; -5%Z] (-11%Z, -20412000%Z).
Proof.
  unfold sum_product_spec.
  compute.
  reflexivity.
Qed.