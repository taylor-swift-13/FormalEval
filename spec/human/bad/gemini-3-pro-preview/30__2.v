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

Example test_get_positive : problem_30_spec [5; 3; -5; 2; 3; 3; 9; 0; 123; 1; -10] [5; 3; 2; 3; 3; 9; 123; 1].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: subsequence *)
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_nil.
  - (* Part 2: equivalence *)
    intro r.
    unfold is_positive.
    split.
    + (* In output -> In input /\ r > 0 *)
      intro H_in_out.
      simpl in H_in_out.
      repeat destruct H_in_out as [H_eq | H_in_out]; subst r.
      * split. { simpl. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. do 3 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. do 6 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. do 8 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
      * split. { simpl. do 9 right. left. reflexivity. } { apply IZR_lt. reflexivity. }
    + (* In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      repeat destruct H_in_in as [H_eq | H_in_in]; subst r.
      * simpl. left. reflexivity.
      * simpl. right. left. reflexivity.
      * exfalso. assert (Hneg: -5 < 0) by (apply IZR_lt; reflexivity). apply (Rlt_asym _ _ Hneg H_pos).
      * simpl. do 2 right. left. reflexivity.
      * simpl. right. left. reflexivity.
      * simpl. right. left. reflexivity.
      * simpl. do 5 right. left. reflexivity.
      * exfalso. apply (Rlt_irrefl 0 H_pos).
      * simpl. do 6 right. left. reflexivity.
      * simpl. do 7 right. left. reflexivity.
      * exfalso. assert (Hneg: -10 < 0) by (apply IZR_lt; reflexivity). apply (Rlt_asym _ _ Hneg H_pos).
Qed.