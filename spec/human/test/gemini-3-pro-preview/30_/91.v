Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope R_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_get_positive : problem_30_spec [1; -1; 2; -2; -3; 4; -4; 0; 0; 0] [1; 2; 4].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: subsequence *)
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_nil.
  - (* Part 2: equivalence *)
    intro r.
    unfold is_positive.
    split.
    + (* In output -> In input /\ r > 0 *)
      intro H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H1 | [H2 | [H4 | H_nil]]].
      * subst r. split.
        { simpl. left. reflexivity. }
        { apply IZR_lt. reflexivity. }
      * subst r. split.
        { simpl. right. right. left. reflexivity. }
        { apply IZR_lt. reflexivity. }
      * subst r. split.
        { simpl. right. right. right. right. right. left. reflexivity. }
        { apply IZR_lt. reflexivity. }
      * contradiction.
    + (* In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H1 | [Hn1 | [H2 | [Hn2 | [Hn3 | [H4 | [Hn4 | [H0_1 | [H0_2 | [H0_3 | H_nil]]]]]]]]]].
      * subst r. simpl. left. reflexivity.
      * subst r.
        assert (Hneg: -1 < 0) by (apply IZR_lt; reflexivity).
        exfalso. apply (Rlt_asym _ _ Hneg H_pos).
      * subst r. simpl. right. left. reflexivity.
      * subst r.
        assert (Hneg: -2 < 0) by (apply IZR_lt; reflexivity).
        exfalso. apply (Rlt_asym _ _ Hneg H_pos).
      * subst r.
        assert (Hneg: -3 < 0) by (apply IZR_lt; reflexivity).
        exfalso. apply (Rlt_asym _ _ Hneg H_pos).
      * subst r. simpl. right. right. left. reflexivity.
      * subst r.
        assert (Hneg: -4 < 0) by (apply IZR_lt; reflexivity).
        exfalso. apply (Rlt_asym _ _ Hneg H_pos).
      * subst r. exfalso. apply (Rlt_irrefl 0 H_pos).
      * subst r. exfalso. apply (Rlt_irrefl 0 H_pos).
      * subst r. exfalso. apply (Rlt_irrefl 0 H_pos).
      * contradiction.
Qed.