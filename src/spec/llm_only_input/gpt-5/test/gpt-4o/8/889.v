Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_given_list :
  sum_product_spec (1%Z :: -2%Z :: -6%Z :: -1%Z :: 0%Z :: -1%Z :: nil) (-9%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.