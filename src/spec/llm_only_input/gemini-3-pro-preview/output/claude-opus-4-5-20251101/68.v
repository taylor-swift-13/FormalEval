Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_even (n : Z) : Prop := Z.even n = true.

Definition is_odd (n : Z) : Prop := Z.odd n = true.

Definition all_odd (arr : list Z) : Prop :=
  forall x, In x arr -> is_odd x.

Definition has_even (arr : list Z) : Prop :=
  exists x, In x arr /\ is_even x.

Definition is_smallest_even (arr : list Z) (v : Z) : Prop :=
  In v arr /\
  is_even v /\
  forall x, In x arr -> is_even x -> v <= x.

Definition is_first_index_of (arr : list Z) (v : Z) (idx : nat) : Prop :=
  (idx < length arr)%nat /\
  nth idx arr 0 = v /\
  forall j, (j < idx)%nat -> nth j arr 0 <> v.

Definition pluck_spec (arr : list Z) (result : list Z) : Prop :=
  (arr = [] -> result = []) /\
  (arr <> [] -> all_odd arr -> result = []) /\
  (arr <> [] -> has_even arr ->
    exists min_even idx,
      is_smallest_even arr min_even /\
      is_first_index_of arr min_even idx /\
      result = [min_even; Z.of_nat idx]).

Example test_pluck : pluck_spec [4; 2; 3] [2; 1].
Proof.
  unfold pluck_spec.
  split.
  - (* Case 1: arr = [] *)
    intro H. discriminate H.
  - split.
    + (* Case 2: arr <> [] -> all_odd *)
      intros _ H_all.
      assert (In 4 [4; 2; 3]) as H_in4. { simpl. auto. }
      specialize (H_all 4 H_in4).
      unfold is_odd in H_all. simpl in H_all. discriminate H_all.
    + (* Case 3: arr <> [] -> has_even *)
      intros _ _.
      exists 2, 1%nat.
      split.
      * (* is_smallest_even *)
        unfold is_smallest_even.
        split.
        -- simpl. auto.
        -- split.
           ++ unfold is_even. reflexivity.
           ++ intros x H_in H_even.
              simpl in H_in.
              destruct H_in as [H4 | [H2 | [H3 | H_false]]].
              ** subst. lia.
              ** subst. lia.
              ** subst. unfold is_even in H_even. simpl in H_even. discriminate H_even.
              ** contradiction.
      * split.
        -- (* is_first_index_of *)
           unfold is_first_index_of.
           split.
           ++ simpl. lia.
           ++ split.
              ** simpl. reflexivity.
              ** intros j H_lt.
                 assert (j = 0%nat) by lia.
                 subst. simpl. discriminate.
        -- (* result equality *)
           simpl. reflexivity.
Qed.