Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Lemma problem_29_example : problem_29_spec ["hello"; "world"; "heworldlo"; "house"] "h" ["hello"; "heworldlo"; "house"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros s.
    split.
    + intros H_in.
      simpl in H_in.
      destruct H_in as [H_hello | [H_heworldlo | [H_house | H_false]]].
      * subst.
        split.
        -- simpl. left. reflexivity.
        -- reflexivity.
      * subst.
        split.
        -- simpl. right. right. left. reflexivity.
        -- reflexivity.
      * subst.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- reflexivity.
      * contradiction.
    + intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_hello | [H_world | [H_heworldlo | [H_house | H_false]]]].
      * subst.
        simpl. left. reflexivity.
      * subst.
        simpl in H_prefix.
        discriminate H_prefix.
      * subst.
        simpl. right. left. reflexivity.
      * subst.
        simpl. right. right. left. reflexivity.
      * contradiction.
Qed.