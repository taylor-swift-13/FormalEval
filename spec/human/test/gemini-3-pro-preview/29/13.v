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

Example problem_29_test : problem_29_spec ["hello"; "world"; "heworldlo"; "house"] "h" ["hello"; "heworldlo"; "house"].
Proof.
  unfold problem_29_spec.
  split.
  - simpl.
    left. split; [reflexivity | ].
    right.
    left. split; [reflexivity | ].
    left. split; [reflexivity | ].
    trivial.
  - intros s.
    split.
    + intros H.
      simpl in H.
      destruct H as [H1 | [H2 | [H3 | H4]]].
      * subst s.
        split.
        -- simpl. left. reflexivity.
        -- simpl. reflexivity.
      * subst s.
        split.
        -- simpl. right. right. left. reflexivity.
        -- simpl. reflexivity.
      * subst s.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- simpl. reflexivity.
      * contradiction.
    + intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | H5]]]].
      * subst s.
        simpl. left. reflexivity.
      * subst s.
        simpl in H_prefix. discriminate H_prefix.
      * subst s.
        simpl. right. left. reflexivity.
      * subst s.
        simpl. right. right. left. reflexivity.
      * contradiction.
Qed.