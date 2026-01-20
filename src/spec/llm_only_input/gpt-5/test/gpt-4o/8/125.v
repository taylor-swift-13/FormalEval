Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec (4 :: -6 :: 0 :: 8 :: -10 :: nil) (-4, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.