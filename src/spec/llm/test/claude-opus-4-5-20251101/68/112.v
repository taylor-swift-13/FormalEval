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

Definition test_input : list Z :=
  [10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 0%Z].

Example pluck_test1 : pluck_spec test_input [0%Z; 63%Z].
Proof.
  unfold pluck_spec.
  split; [| split].
  - intro H. unfold test_input in H. discriminate H.
  - intros _ Hodd.
    unfold all_odd in Hodd.
    exfalso.
    specialize (Hodd 10000%Z).
    assert (In 10000%Z test_input) as Hin.
    { unfold test_input. simpl. left. reflexivity. }
    specialize (Hodd Hin).
    unfold is_odd in Hodd.
    simpl in Hodd.
    discriminate Hodd.
  - intros _ _.
    exists 0%Z, 63%nat.
    split; [| split].
    + unfold is_smallest_even.
      split; [| split].
      * unfold test_input. simpl.
        do 63 right. left. reflexivity.
      * unfold is_even. simpl. reflexivity.
      * intros x Hin Heven.
        unfold test_input in Hin.
        simpl in Hin.
        repeat (destruct Hin as [Hin | Hin]; [subst x; lia || (unfold is_even in Heven; simpl in Heven; discriminate Heven) |]).
        contradiction.
    + unfold is_first_index_of.
      split; [| split].
      * unfold test_input. simpl. lia.
      * unfold test_input. simpl. reflexivity.
      * intros j Hj.
        unfold test_input.
        assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31 \/ j = 32 \/ j = 33 \/ j = 34 \/ j = 35 \/ j = 36 \/ j = 37 \/ j = 38 \/ j = 39 \/ j = 40 \/ j = 41 \/ j = 42 \/ j = 43 \/ j = 44 \/ j = 45 \/ j = 46 \/ j = 47 \/ j = 48 \/ j = 49 \/ j = 50 \/ j = 51 \/ j = 52 \/ j = 53 \/ j = 54 \/ j = 55 \/ j = 56 \/ j = 57 \/ j = 58 \/ j = 59 \/ j = 60 \/ j = 61 \/ j = 62)%nat as Hcases by lia.
        repeat (destruct Hcases as [Hcases | Hcases]; [subst j; simpl; lia |]).
        subst j. simpl. lia.
    + simpl. reflexivity.
Qed.