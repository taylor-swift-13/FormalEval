Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negatives_and_zero :
  sum_product_spec
    (cons (Z.opp 6%Z) (cons 2%Z (cons 3%Z (cons (Z.opp 6%Z) (cons 0%Z (cons 8%Z (cons (Z.opp 10%Z) nil)))))))
    (Z.opp 9%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.