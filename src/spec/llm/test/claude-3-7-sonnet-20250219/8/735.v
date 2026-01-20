Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Fixpoint bool_list_sum_product (bl : list bool) : nat * nat :=
  match bl with
  | [] => (0, 1)
  | b :: bs =>
    let (s, p) := bool_list_sum_product bs in
    let v := if b then 1 else 0 in
    (s + v, p * v)
  end.

Definition sum_product_spec (numbers : list (list bool)) (result_sum result_product : nat) : Prop :=
  let sums_products := map bool_list_sum_product numbers in
  result_sum = fold_left (fun acc sp => acc + fst sp) sums_products 0 /\
  result_product = fold_left (fun acc sp => acc * snd sp) sums_products 1.

Example test_sum_product_single_true_list :
  sum_product_spec [[true]] 1 1.
Proof.
  unfold sum_product_spec.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.