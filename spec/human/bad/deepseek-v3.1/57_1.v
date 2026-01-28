Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition monotonic (l: list Z) : bool :=
  match l with
  | nil => true
  | h::t =>
      match t with
      | nil => true
      | a::t' =>
          if Z_le_gt_dec h a then
            forallb (fun p => Z.leb (fst p) (snd p)) (combine l (tl l))
          else
            forallb (fun p => Z.leb (snd p) (fst p)) (combine l (tl l))
      end
  end.

Lemma forallb_combine_sorted_le : forall (l : list Z),
  (forallb (fun p => Z.leb (fst p) (snd p)) (combine l (tl l)) = true) <->
  (forall i, (i < length l - 1)%nat -> (nth i l 0 <= nth (S i) l 0)%Z).
Proof.
  intros l. split.
  - intro H. apply forallb_forall in H.
    intros i Hi. 
    assert (Hin : In (nth i l 0, nth (S i) l 0) (combine l (tl l))).
    { apply nth_In_combine; lia. }
    apply H in Hin. simpl in Hin.
    apply Z.leb_le in Hin. assumption.
  - intro H. apply forallb_forall.
    intros [x y] Hin.
    apply in_combine_lr in Hin.
    destruct Hin as [i [Hi1 Hi2]].
    rewrite Hi1, Hi2.
    apply Z.leb_le. apply H.
    destruct (lt_dec i (length l - 1)%nat).
    + assumption.
    + lia.
Qed.

Lemma forallb_combine_sorted_ge : forall (l : list Z),
  (forallb (fun p => Z.leb (snd p) (fst p)) (combine l (tl l)) = true) <->
  (forall i, (i < length l - 1)%nat -> (nth (S i) l 0 <= nth i l 0)%Z).
Proof.
  intros l. split.
  - intro H. apply forallb_forall in H.
    intros i Hi. 
    assert (Hin : In (nth i l 0, nth (S i) l 0) (combine l (tl l))).
    { apply nth_In_combine; lia. }
    apply H in Hin. simpl in Hin.
    apply Z.leb_le in Hin. assumption.
  - intro H. apply forallb_forall.
    intros [x y] Hin.
    apply in_combine_lr in Hin.
    destruct Hin as [i [Hi1 Hi2]].
    rewrite Hi1, Hi2.
    apply Z.leb_le. apply H.
    destruct (lt_dec i (length l - 1)%nat).
    + assumption.
    + lia.
Qed.

Lemma monotonic_correct : forall (l: list Z),
  monotonic l = true <-> (Sorted Z.le l \/ Sorted Z.ge l).
Proof.
  intros l. split.
  - intro H. unfold monotonic in H.
    destruct l as [|h t].
    + left. apply Sorted_nil.
    + destruct t as [|a t'].
      * left. constructor. constructor.
      * destruct (Z_le_gt_dec h a) as [Hle|Hgt].
        { 
          apply forallb_combine_sorted_le in H.
          left.
          induction t' as [|b t'' IH].
          - constructor.
            + apply Z.le_refl.
            + constructor.
          - constructor.
            + apply IH.
              intros j Hj.
              apply H. simpl. lia.
            + apply H. simpl. lia.
        }
        {
          apply forallb_combine_sorted_ge in H.
          right.
          induction t' as [|b t'' IH].
          - constructor.
            + apply Z.le_refl.
            + constructor.
          - constructor.
            + apply IH.
              intros j Hj.
              apply H. simpl. lia.
            + apply H. simpl. lia.
        }
  - intro H. unfold monotonic.
    destruct l as [|h t].
    + reflexivity.
    + destruct t as [|a t'].
      * reflexivity.
      * destruct H as [Hinc|Hdec].
        {
          destruct (Z_le_gt_dec h a) as [Hle|Hgt].
          - apply forallb_combine_sorted_le.
            intros i Hi.
            apply Sorted_nth with (d := 0%Z); try lia.
            apply Hinc.
          - exfalso.
            apply Zgt_not_le in Hgt.
            apply Hgt.
            apply Sorted_nth with (d := 0%Z) (i := 0) in Hinc; try lia.
            simpl in Hinc. assumption.
        }
        {
          destruct (Z_le_gt_dec h a) as [Hle|Hgt].
          - exfalso.
            apply Zle_gt_dec in Hle.
            destruct Hle as [Hlt|Heq].
            + apply Sorted_nth with (d := 0%Z) (i := 0) in Hdec; try lia.
              simpl in Hdec.
              lia.
            + apply Sorted_nth with (d := 0%Z) (i := 0) in Hdec; try lia.
              simpl in Hdec.
              lia.
          - apply forallb_combine_sorted_ge.
            intros i Hi.
            assert (Hrev : Sorted Z.le (rev (h :: a :: t'))).
            { apply Sorted_rev. assumption. }
            apply Sorted_nth with (d := 0%Z) in Hrev; try lia.
            rewrite rev_length in Hrev. simpl in Hrev.
            rewrite nth_rev in Hrev; try lia.
            rewrite nth_rev in Hrev; try lia.
            simpl in Hrev. assumption.
        }
Qed.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example test_monotonic : problem_57_spec [1%Z; 2%Z; 4%Z; 10%Z] true.
Proof.
  unfold problem_57_spec. split.
  - intro H. left.
    repeat constructor; lia.
  - intro. reflexivity.
Qed.