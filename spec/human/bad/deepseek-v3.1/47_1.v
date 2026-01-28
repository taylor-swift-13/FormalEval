Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Fixpoint sorted_insert (x : R) (l : list R) : list R :=
  match l with
  | [] => [x]
  | h :: t => if Rle_dec x h then x :: h :: t else h :: sorted_insert x t
  end.

Fixpoint insertion_sort (l : list R) : list R :=
  match l with
  | [] => []
  | h :: t => sorted_insert h (insertion_sort t)
  end.

Lemma insertion_sort_sorted : forall l, Sorted Rle (insertion_sort l).
Proof.
  induction l; simpl.
  - constructor.
  - assert (H: Sorted Rle (insertion_sort l)) by apply IHl.
    induction (insertion_sort l); simpl.
    + constructor; [constructor|].
    + destruct (Rle_dec a r).
      * constructor; auto.
        constructor; auto.
        apply Sorted_inv in H; destruct H; auto.
      * constructor; auto.
        apply IHl0; auto.
        apply Sorted_inv in H; destruct H; auto.
Qed.

Lemma insertion_sort_permutation : forall l x, In x l <-> In x (insertion_sort l).
Proof.
  split.
  - induction l; simpl; intros.
    + inversion H.
    + inversion H.
      * subst a. clear H.
        induction (insertion_sort l); simpl.
        -- left; reflexivity.
        -- destruct (Rle_dec a r).
           ++ left; reflexivity.
           ++ right; auto.
      * specialize (IHl H0).
        induction (insertion_sort l); simpl.
        -- right; auto.
        -- destruct (Rle_dec a r).
           ++ right; auto.
           ++ destruct IHl.
              ** left; auto.
              ** right; auto.
  - induction l; simpl; intros.
    + inversion H.
    + induction (insertion_sort l); simpl in H.
      * inversion H.
      * destruct (Rle_dec a r).
        ++ destruct H.
           ** subst r. right.
              apply IHl. left; reflexivity.
           ** destruct H.
              *** subst a. left; reflexivity.
              *** right. apply IHl. right; auto.
        ++ destruct H.
           ** subst r. right.
              apply IHl. left; reflexivity.
           ** destruct H.
              *** subst h. left; reflexivity.
              *** right. apply IHl. right; auto.
Qed.

Definition median (l : list R) : R :=
  let sorted_l := insertion_sort l in
  let len := length l in
  let halflen := (len / 2)%nat in
  match (len mod 2)%nat with
  | 1%nat => nth halflen sorted_l 0
  | _ => ((nth halflen sorted_l 0) + (nth (halflen-1)%nat sorted_l 0)) / 2
  end.

Example test_median : median [3; 1; 2; 4; 5] = 3.
Proof.
  unfold median.
  simpl.
  reflexivity.
Qed.

Lemma median_spec : forall (input : list R), input <> [] -> problem_47_spec input (median input).
Proof.
  intros input Hnonempty.
  unfold problem_47_spec.
  exists (insertion_sort input).
  split.
  - apply insertion_sort_sorted.
  - intros r.
    split.
    + intro Hin.
      split.
      * apply insertion_sort_permutation; auto.
      * unfold median.
        simpl.
        split; intros Hmod; simpl.
        { reflexivity. }
        { reflexivity. }
    - intros [Hin _].
      apply insertion_sort_permutation in Hin.
      auto.
Qed.