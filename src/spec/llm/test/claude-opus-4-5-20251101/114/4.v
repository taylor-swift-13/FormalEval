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

Lemma singleton_subarray_of_singleton : forall (x : Z),
  is_subarray [x] [x] -> sum_list [x] = x.
Proof.
  intros x H.
  simpl. lia.
Qed.

Lemma only_subarray_of_singleton : forall (sub : list Z) (x : Z),
  is_subarray sub [x] -> non_empty sub -> sub = [x].
Proof.
  intros sub x [prefix [suffix Heq]] Hne.
  destruct prefix as [|p ps].
  - simpl in Heq.
    destruct sub as [|s ss].
    + unfold non_empty in Hne. exfalso. apply Hne. reflexivity.
    + simpl in Heq.
      injection Heq as Hs Hsuff.
      destruct ss as [|s2 ss2].
      * simpl in Hsuff. subst. reflexivity.
      * simpl in Hsuff. destruct suffix; discriminate.
  - simpl in Heq.
    injection Heq as Hp Hrest.
    destruct ps as [|p2 ps2].
    + simpl in Hrest.
      destruct sub as [|s ss].
      * unfold non_empty in Hne. exfalso. apply Hne. reflexivity.
      * simpl in Hrest. destruct ss; destruct suffix; discriminate.
    + simpl in Hrest. discriminate.
Qed.

Example test_minSubArraySum : minSubArraySum_spec [-9999999999999999] (-9999999999999999).
Proof.
  unfold minSubArraySum_spec.
  split.
  - discriminate.
  - split.
    + exists [-9999999999999999].
      split.
      * unfold non_empty. discriminate.
      * split.
        -- unfold is_subarray.
           exists [], [].
           reflexivity.
        -- simpl. lia.
    + intros sub Hne Hsub.
      assert (Heq: sub = [-9999999999999999]).
      {
        apply only_subarray_of_singleton; assumption.
      }
      rewrite Heq.
      simpl. lia.
Qed.