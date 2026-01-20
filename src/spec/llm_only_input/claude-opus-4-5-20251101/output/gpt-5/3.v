Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_empty_list : below_zero_spec [] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* result = true <-> exists prefix suffix, ... *)
    split.
    + (* true -> exists ... *)
      intros H. discriminate H.
    + (* exists ... -> true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix.
      * (* prefix = [] *)
        simpl in Hsum. unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix = z :: prefix *)
        simpl in Heq. discriminate Heq.
  - (* result = false <-> forall prefix suffix, ... *)
    split.
    + (* false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix.
      * (* prefix = [] *)
        unfold sum_list. simpl. lia.
      * (* prefix = z :: prefix *)
        simpl in Heq. discriminate Heq.
    + (* forall ... -> false *)
      intros _. reflexivity.
Qed.