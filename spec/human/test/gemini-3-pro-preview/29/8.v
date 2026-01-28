Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example problem_29_test : problem_29_spec ["a"; "ab"; "abc"; "ba"; "bb"; "bc"] "a" ["a"; "ab"; "abc"].
Proof.
  unfold problem_29_spec.
  split.
  - simpl.
    left. split. reflexivity.
    left. split. reflexivity.
    left. split. reflexivity.
    simpl. trivial.
  - intros s.
    split.
    + intros H.
      simpl in H.
      destruct H as [H | [H | [H | H]]].
      * subst. split.
        -- simpl. left. reflexivity.
        -- simpl. reflexivity.
      * subst. split.
        -- simpl. right. left. reflexivity.
        -- simpl. reflexivity.
      * subst. split.
        -- simpl. right. right. left. reflexivity.
        -- simpl. reflexivity.
      * contradiction.
    + intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | H]]]]]].
      * subst. simpl. left. reflexivity.
      * subst. simpl. right. left. reflexivity.
      * subst. simpl. right. right. left. reflexivity.
      * subst. simpl in H_prefix. discriminate.
      * subst. simpl in H_prefix. discriminate.
      * subst. simpl in H_prefix. discriminate.
      * contradiction.
Qed.