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

Example test_get_positive : problem_30_spec [7; 8; 10; 11; 12; 15; 17; -1] [7; 8; 10; 11; 12; 15; 17].
Proof.
  unfold problem_30_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_nil.
  - intro r.
    unfold is_positive.
    split.
    + intro H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
      * subst r. split. { simpl. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * subst r. split. { simpl. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * subst r. split. { simpl. right. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * subst r. split. { simpl. right. right. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * subst r. split. { simpl. do 4 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * subst r. split. { simpl. do 5 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * subst r. split. { simpl. do 6 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * contradiction.
    + intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
      * subst r. simpl. left. reflexivity.
      * subst r. simpl. right. left. reflexivity.
      * subst r. simpl. right. right. left. reflexivity.
      * subst r. simpl. right. right. right. left. reflexivity.
      * subst r. simpl. do 4 right. left. reflexivity.
      * subst r. simpl. do 5 right. left. reflexivity.
      * subst r. simpl. do 6 right. left. reflexivity.
      * subst r.
        assert (Hneg: -1 < 0) by (apply IZR_lt; reflexivity).
        exfalso. apply (Rlt_asym _ _ Hneg H_pos).
      * contradiction.
Qed.