Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Lia.

Definition is_even (n : nat) : Prop := Nat.even n = true.

Definition pluck_spec (arr : list nat) (result : list nat) : Prop :=
  (result = [] /\ (forall x, In x arr -> Nat.odd x = true)) \/
  (exists min_even idx,
      In min_even arr /\
      is_even min_even /\
      (forall x, In x arr -> is_even x -> min_even <= x) /\
      nth_error arr idx = Some min_even /\
      (forall j, nth_error arr j = Some min_even -> idx <= j) /\
      result = [min_even; idx]).

Example test_pluck : pluck_spec [4; 2; 3] [2; 1].
Proof.
  unfold pluck_spec.
  right.
  exists 2, 1.
  repeat split.
  - (* In min_even arr *)
    simpl. right. left. reflexivity.
  - (* is_even min_even *)
    unfold is_even. simpl. reflexivity.
  - (* Minimal even property *)
    intros x H_in H_even.
    simpl in H_in.
    destruct H_in as [H4 | [H2 | [H3 | H_empty]]].
    + (* x = 4 *)
      subst. lia.
    + (* x = 2 *)
      subst. lia.
    + (* x = 3 *)
      subst. unfold is_even in H_even. simpl in H_even. discriminate.
    + (* False *)
      contradiction.
  - (* nth_error correct *)
    simpl. reflexivity.
  - (* First index property *)
    intros j H_nth.
    destruct j.
    + (* j = 0 *)
      simpl in H_nth. inversion H_nth.
    + (* j >= 1 *)
      lia.
  - (* Result equality *)
    reflexivity.
Qed.