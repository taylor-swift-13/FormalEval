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

Example pluck_spec_test :
  pluck_spec [4%Z; 2%Z; 3%Z] [2%Z; 1%Z].
Proof.
  unfold pluck_spec.
  repeat split.
  - intros H; discriminate H.
  - intros Hne Hall; exfalso.
    assert (Hin4 : In 4%Z [4%Z; 2%Z; 3%Z]) by (simpl; auto).
    specialize (Hall 4%Z Hin4).
    simpl in Hall.
    discriminate Hall.
  - intros Hne Hev.
    exists 2%Z, 1%nat.
    split.
    + unfold is_smallest_even.
      split.
      * simpl; right; left; reflexivity.
      * split.
        -- unfold is_even; simpl; reflexivity.
        -- intros x HIn Hevx.
           simpl in HIn.
           destruct HIn as [Hx | HIn2].
           ++ subst x. lia.
           ++ destruct HIn2 as [Hx | HIn3].
              ** subst x. lia.
              ** destruct HIn3 as [Hx | HIn4].
                 --- subst x. lia.
                 --- contradiction.
    + split.
      * unfold is_first_index_of.
        split.
        -- simpl; lia.
        -- split.
           ++ simpl; reflexivity.
           ++ intros j Hj.
              destruct j as [| j']; simpl.
              ** intros Heq; discriminate Heq.
              ** exfalso; lia.
      * simpl; reflexivity.
Qed.