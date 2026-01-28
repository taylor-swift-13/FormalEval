Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.SetoidList.
Require Import Lia.
Import ListNotations.

Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

Lemma even_digits_between_2_10 : problem_163_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold problem_163_spec.
  split.
  - intro d.
    split.
    + intro H.
      simpl in H.
      destruct H as [H|H].
      * subst d. split. 
        { unfold min. lia. } 
        split. 
        { unfold max. lia. } 
        split. 
        { lia. } 
        { exists 1. lia. }
      * destruct H as [H|H].
        { subst d. split. 
          { unfold min. lia. } 
          split. 
          { unfold max. lia. } 
          split. 
          { lia. } 
          { exists 2. lia. } }
        { destruct H as [H|H].
          { subst d. split. 
            { unfold min. lia. } 
            split. 
            { unfold max. lia. } 
            split. 
            { lia. } 
            { exists 3. lia. } }
          { destruct H as [H|H].
            { subst d. split. 
              { unfold min. lia. } 
              split. 
              { unfold max. lia. } 
              split. 
              { lia. } 
              { exists 4. lia. } }
            { contradiction. } } }
    + intro H.
      destruct H as [Hmin Hmax].
      destruct Hmax as [Hmax Hrest].
      destruct Hrest as [Hlt Heven].
      destruct Heven as [k Heven].
      assert (Hrange: min 2 10 <= d <= max 2 10) by (split; lia).
      simpl in Hrange.
      assert (Hbounds: 2 <= d <= 10) by lia.
      assert (Hlt10: d < 10) by lia.
      simpl.
      destruct d as [| [| [| [| [| [| [| [| [| d]]]]]]]]].
      * lia.
      * lia.
      * left. reflexivity.
      * lia.
      * right. left. reflexivity.
      * lia.
      * right. right. left. reflexivity.
      * lia.
      * right. right. right. left. reflexivity.
      * lia.
  - split.
    + constructor.
      * constructor.
      * constructor.
        { constructor. }
        { constructor; lia. }
      * constructor.
        { constructor. }
        { constructor; lia. }
      * constructor.
        { constructor. }
        { constructor; lia. }
    + constructor.
      * intro H. inversion H.
      * constructor.
        { intro H. inversion H.
          inversion H1. }
        { constructor.
          { intro H. inversion H.
            inversion H1. }
          { constructor.
            { intro H. inversion H.
              inversion H1. }
            { constructor. } } }
Qed.