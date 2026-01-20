Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_large_numbers :
  sum_product_spec (2147483647%Z :: (-2147483648%Z) :: nil) (-1%Z, -4611686016279904256%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  compute.
  reflexivity.
Qed.