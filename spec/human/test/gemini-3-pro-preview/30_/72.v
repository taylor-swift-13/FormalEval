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

Example test_get_positive : problem_30_spec [10; 10; -10; 15; -15; 20; -20; 25; -25; 25] [10; 10; 15; 20; 25; 25].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: subsequence *)
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_nil.
  - (* Part 2: equivalence *)
    intro r.
    unfold is_positive.
    split.
    + (* In output -> In input /\ r > 0 *)
      intro H_in_out.
      simpl in H_in_out.
      repeat destruct H_in_out as [H_eq | H_in_out]; try contradiction; subst r.
      * (* 10 *) split. { simpl. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * (* 10 *) split. { simpl. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * (* 15 *) split. { simpl. right. right. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * (* 20 *) split. { simpl. do 5 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * (* 25 *) split. { simpl. do 7 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * (* 25 *) split. { simpl. do 7 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
    + (* In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      repeat destruct H_in_in as [H_eq | H_in_in]; try contradiction; subst r.
      * (* 10 *) simpl. left. reflexivity.
      * (* 10 *) simpl. left. reflexivity.
      * (* -10 *)
        exfalso.
        assert (Hneg: -10 < 0) by (apply IZR_lt; reflexivity).
        apply (Rlt_asym _ _ Hneg H_pos).
      * (* 15 *) simpl. right. right. left. reflexivity.
      * (* -15 *)
        exfalso.
        assert (Hneg: -15 < 0) by (apply IZR_lt; reflexivity).
        apply (Rlt_asym _ _ Hneg H_pos).
      * (* 20 *) simpl. right. right. right. left. reflexivity.
      * (* -20 *)
        exfalso.
        assert (Hneg: -20 < 0) by (apply IZR_lt; reflexivity).
        apply (Rlt_asym _ _ Hneg H_pos).
      * (* 25 *) simpl. do 4 right. left. reflexivity.
      * (* -25 *)
        exfalso.
        assert (Hneg: -25 < 0) by (apply IZR_lt; reflexivity).
        apply (Rlt_asym _ _ Hneg H_pos).
      * (* 25 *) simpl. do 4 right. left. reflexivity.
Qed.