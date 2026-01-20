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

Example pluck_test2 : pluck_spec [1%Z; 303%Z; 5%Z; 7%Z; 9%Z; 5%Z] [].
Proof.
  unfold pluck_spec.
  split; [| split].
  - intro H. discriminate H.
  - intros _ Hodd.
    reflexivity.
  - intros _ Heven.
    unfold has_even in Heven.
    destruct Heven as [x [Hin Heven]].
    simpl in Hin.
    destruct Hin as [H | [H | [H | [H | [H | [H | H]]]]]].
    + subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
    + subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
    + subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
    + subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
    + subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
    + subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
    + contradiction.
Qed.