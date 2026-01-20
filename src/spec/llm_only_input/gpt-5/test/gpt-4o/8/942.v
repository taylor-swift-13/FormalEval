Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (4 :: -6 :: -7 :: -1 :: 30 :: -10 :: -10 :: -6 :: nil) (-6, 3024000).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.