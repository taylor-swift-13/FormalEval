Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_1: sum_product_spec [78; -77; 91; -36; 6; -2; -74; 20; 93; 20] (119, 649957750041600).
Proof.
  unfold sum_product_spec.
  reflexivity.
Qed.