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

Example test_sum_product : sum_product_spec [78; -77; 91; -36; 6; -2; -74; 20; 27; 93] (126, 877442962556160).
Proof.
  unfold sum_product_spec.
  simpl.
  split; reflexivity.
Qed.