(* HumanEval 8 - Inductive Spec *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_product_fold : list Z -> Z -> Z -> Prop :=
| spf_nil : sum_product_fold [] 0%Z 1%Z
| spf_cons : forall h t s p s' p',
    sum_product_fold t s p ->
    s' = s + h -> p' = p * h ->
    sum_product_fold (h :: t) s' p'.

Definition sum_product_spec (l : list Z) (output : Z * Z) : Prop :=
  let '(s, p) := output in
  sum_product_fold l s p.

Example sum_product_spec_nil: sum_product_spec nil (0%Z, 1%Z).
Proof.
  unfold sum_product_spec.
  simpl. constructor.
Qed.

Example sum_product_spec_1_2_3: sum_product_spec (1%Z :: 2%Z :: 3%Z :: nil) (6%Z, 6%Z).
Proof.
  unfold sum_product_spec.
  apply (spf_cons 1%Z (2%Z :: 3%Z :: nil) 5%Z 6%Z 6%Z 6%Z).
  - apply (spf_cons 2%Z (3%Z :: nil) 3%Z 3%Z 5%Z 6%Z).
    + apply (spf_cons 3%Z nil 0%Z 1%Z 3%Z 3%Z).
      * constructor.
      * reflexivity.
      * reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

