Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_example : below_zero_spec [1%Z; 2%Z; 3%Z; -6%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 prefix']]]]]; simpl in Heq.
      * unfold sum_list in Hsum. simpl in Hsum. lia.
      * injection Heq as Hz1 H. subst. unfold sum_list in Hsum. simpl in Hsum. lia.
      * injection Heq as Hz1 Hz2 H. subst. unfold sum_list in Hsum. simpl in Hsum. lia.
      * injection Heq as Hz1 Hz2 Hz3 H. subst. unfold sum_list in Hsum. simpl in Hsum. lia.
      * injection Heq as Hz1 Hz2 Hz3 Hz4 H. subst. unfold sum_list in Hsum. simpl in Hsum. lia.
      * discriminate Heq.
  - split.
    + intros _ prefix suffix Heq.
      destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 prefix']]]]]; simpl in Heq.
      * unfold sum_list. simpl. lia.
      * injection Heq as Hz1 H. subst. unfold sum_list. simpl. lia.
      * injection Heq as Hz1 Hz2 H. subst. unfold sum_list. simpl. lia.
      * injection Heq as Hz1 Hz2 Hz3 H. subst. unfold sum_list. simpl. lia.
      * injection Heq as Hz1 Hz2 Hz3 Hz4 H. subst. unfold sum_list. simpl. lia.
      * discriminate Heq.
    + intro H. reflexivity.
Qed.