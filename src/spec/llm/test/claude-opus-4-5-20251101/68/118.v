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

Example pluck_test1 : pluck_spec [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 34%Z; 37%Z; 39%Z; 4%Z; 2%Z] [2%Z; 21%Z].
Proof.
  unfold pluck_spec.
  split; [| split].
  - intro H. discriminate H.
  - intros _ Hodd.
    unfold all_odd in Hodd.
    exfalso.
    specialize (Hodd 34%Z).
    assert (In 34%Z [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 34%Z; 37%Z; 39%Z; 4%Z; 2%Z]) as Hin.
    { simpl. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity. }
    specialize (Hodd Hin).
    unfold is_odd in Hodd.
    simpl in Hodd.
    discriminate Hodd.
  - intros _ _.
    exists 2%Z, 21%nat.
    split; [| split].
    + unfold is_smallest_even.
      split; [| split].
      * simpl. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
      * unfold is_even. simpl. reflexivity.
      * intros x Hin Heven.
        simpl in Hin.
        destruct Hin as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]]]]]]]]]].
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. lia.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- subst x. lia.
        -- subst x. lia.
        -- contradiction.
    + unfold is_first_index_of.
      split; [| split].
      * simpl. lia.
      * simpl. reflexivity.
      * intros j Hj.
        destruct j as [| j']; simpl; try lia.
        destruct j' as [| j'']; simpl; try lia.
        destruct j'' as [| j''']; simpl; try lia.
        destruct j''' as [| j'''']; simpl; try lia.
        destruct j'''' as [| j5]; simpl; try lia.
        destruct j5 as [| j6]; simpl; try lia.
        destruct j6 as [| j7]; simpl; try lia.
        destruct j7 as [| j8]; simpl; try lia.
        destruct j8 as [| j9]; simpl; try lia.
        destruct j9 as [| j10]; simpl; try lia.
        destruct j10 as [| j11]; simpl; try lia.
        destruct j11 as [| j12]; simpl; try lia.
        destruct j12 as [| j13]; simpl; try lia.
        destruct j13 as [| j14]; simpl; try lia.
        destruct j14 as [| j15]; simpl; try lia.
        destruct j15 as [| j16]; simpl; try lia.
        destruct j16 as [| j17]; simpl; try lia.
        destruct j17 as [| j18]; simpl; try lia.
        destruct j18 as [| j19]; simpl; try lia.
        destruct j19 as [| j20]; simpl; try lia.
        destruct j20 as [| j21]; simpl; try lia.
    + simpl. reflexivity.
Qed.