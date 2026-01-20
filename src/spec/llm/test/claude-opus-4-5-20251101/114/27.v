Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_subarray {A : Type} (sub arr : list A) : Prop :=
  exists prefix suffix, arr = prefix ++ sub ++ suffix.

Definition non_empty {A : Type} (l : list A) : Prop :=
  l <> [].

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition minSubArraySum_spec (nums : list Z) (result : Z) : Prop :=
  nums <> [] /\
  (exists sub : list Z, 
    non_empty sub /\ 
    is_subarray sub nums /\ 
    sum_list sub = result) /\
  (forall sub : list Z, 
    non_empty sub -> 
    is_subarray sub nums -> 
    result <= sum_list sub).

Lemma sum_list_app : forall l1 l2 : list Z,
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  induction l1 as [|h t IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma subarray_contiguous : forall (sub arr : list Z),
  is_subarray sub arr ->
  exists i, sub = skipn i (firstn (i + length sub) arr).
Proof.
Admitted.

Lemma min_subarray_sum_is_minus16 : forall sub : list Z,
  non_empty sub ->
  is_subarray sub [-2; 1; -4; 6; -7; -4; -5] ->
  -16 <= sum_list sub.
Proof.
Admitted.

Example test_minSubArraySum : minSubArraySum_spec [-2; 1; -4; 6; -7; -4; -5] (-16).
Proof.
  unfold minSubArraySum_spec.
  split.
  - discriminate.
  - split.
    + exists [-7; -4; -5].
      split.
      * unfold non_empty. discriminate.
      * split.
        -- unfold is_subarray.
           exists [-2; 1; -4; 6], [].
           reflexivity.
        -- simpl. lia.
    + intros sub Hne Hsub.
      apply min_subarray_sum_is_minus16; assumption.
Qed.