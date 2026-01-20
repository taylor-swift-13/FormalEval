Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint prod_list (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * prod_list xs
  end.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  res = (sum_list numbers, prod_list numbers).

Example test_case_sum_product_new : sum_product_spec [21%Z; 0%Z; 8%Z; 0%Z] (29, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  replace (21 + (0 + (8 + (0 + 0)))) with 29 by lia.
  replace (21 * (0 * (8 * (0 * 1)))) with 0.
  - reflexivity.
  - rewrite Z.mul_0_l.
    rewrite Z.mul_0_r.
    reflexivity.
Qed.