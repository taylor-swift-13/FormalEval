Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_list (numbers : list Z) : Z :=
  match numbers with
  | [] => 0
  | n :: rest => n + sum_list rest
  end.

Fixpoint product_list (numbers : list Z) : Z :=
  match numbers with
  | [] => 1
  | n :: rest => n * product_list rest
  end.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  fst result = sum_list numbers /\ snd result = product_list numbers.

Example test_sum_product_1 : sum_product_spec [2%Z; 4%Z; 8%Z; 16%Z; 4%Z; 16%Z; 16%Z; 5%Z; -1%Z; 4%Z; 16%Z] (90%Z, -335544320%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.