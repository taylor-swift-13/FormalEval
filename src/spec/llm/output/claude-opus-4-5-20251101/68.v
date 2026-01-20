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

Example pluck_test1 : pluck_spec [4%Z; 2%Z; 3%Z] [2%Z; 1%Z].
Proof.
  unfold pluck_spec.
  split; [| split].
  - (* arr = [] -> result = [] *)
    intro H. discriminate H.
  - (* arr <> [] -> all_odd arr -> result = [] *)
    intros _ Hodd.
    unfold all_odd in Hodd.
    exfalso.
    specialize (Hodd 4%Z).
    assert (In 4%Z [4%Z; 2%Z; 3%Z]) as Hin.
    { simpl. left. reflexivity. }
    specialize (Hodd Hin).
    unfold is_odd in Hodd.
    simpl in Hodd.
    discriminate Hodd.
  - (* arr <> [] -> has_even arr -> exists min_even idx, ... *)
    intros _ _.
    exists 2%Z, 1%nat.
    split; [| split].
    + (* is_smallest_even [4; 2; 3] 2 *)
      unfold is_smallest_even.
      split; [| split].
      * (* In 2 [4; 2; 3] *)
        simpl. right. left. reflexivity.
      * (* is_even 2 *)
        unfold is_even. simpl. reflexivity.
      * (* forall x, In x arr -> is_even x -> 2 <= x *)
        intros x Hin Heven.
        simpl in Hin.
        destruct Hin as [H | [H | [H | H]]].
        -- subst x. lia.
        -- subst x. lia.
        -- subst x. unfold is_even in Heven. simpl in Heven. discriminate Heven.
        -- contradiction.
    + (* is_first_index_of [4; 2; 3] 2 1 *)
      unfold is_first_index_of.
      split; [| split].
      * (* 1 < length [4; 2; 3] *)
        simpl. lia.
      * (* nth 1 [4; 2; 3] 0 = 2 *)
        simpl. reflexivity.
      * (* forall j, j < 1 -> nth j [4; 2; 3] 0 <> 2 *)
        intros j Hj.
        assert (j = 0)%nat as Hj0 by lia.
        subst j.
        simpl.
        lia.
    + (* result = [2; 1] *)
      simpl. reflexivity.
Qed.