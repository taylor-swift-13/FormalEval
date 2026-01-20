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

Lemma subarray_of_singleton : forall (sub : list Z) (x : Z),
  is_subarray sub [x] ->
  sub = [] \/ sub = [x].
Proof.
  intros sub x [prefix [suffix Heq]].
  destruct prefix as [|p ps].
  - simpl in Heq.
    destruct sub as [|s ss].
    + left. reflexivity.
    + simpl in Heq. injection Heq as Hs Hsuffix.
      destruct ss as [|s' ss'].
      * right. rewrite Hs. reflexivity.
      * simpl in Hsuffix. destruct suffix; discriminate.
  - simpl in Heq. injection Heq as Hp Hrest.
    destruct ps as [|p' ps'].
    + simpl in Hrest.
      destruct sub as [|s ss].
      * left. reflexivity.
      * simpl in Hrest. discriminate.
    + simpl in Hrest. discriminate.
Qed.

Lemma non_empty_subarray_of_singleton : forall (sub : list Z) (x : Z),
  non_empty sub ->
  is_subarray sub [x] ->
  sub = [x].
Proof.
  intros sub x Hne Hsub.
  destruct (subarray_of_singleton sub x Hsub) as [H | H].
  - unfold non_empty in Hne. exfalso. apply Hne. exact H.
  - exact H.
Qed.

Example test_minSubArraySum : minSubArraySum_spec [-10] (-10).
Proof.
  unfold minSubArraySum_spec.
  split.
  - discriminate.
  - split.
    + exists [-10].
      split.
      * unfold non_empty. discriminate.
      * split.
        -- unfold is_subarray.
           exists [], [].
           reflexivity.
        -- reflexivity.
    + intros sub Hne Hsub.
      assert (Heq: sub = [-10]).
      {
        apply non_empty_subarray_of_singleton; assumption.
      }
      rewrite Heq.
      simpl.
      lia.
Qed.