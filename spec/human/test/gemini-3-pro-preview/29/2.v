Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Definition provided in the specification *)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(* Pre-condition definition *)
Definition problem_29_pre (input : list string) : Prop := True.

(* Specification definition *)
Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

(* Test case: input = ["xxx"; "asd"; "xxy"; "john doe"; "xxxAAA"; "xxx"], substring = "xxx", output = ["xxx"; "xxxAAA"; "xxx"] *)
Example problem_29_test : problem_29_spec ["xxx"; "asd"; "xxy"; "john doe"; "xxxAAA"; "xxx"] "xxx" ["xxx"; "xxxAAA"; "xxx"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    left. split; [reflexivity | ].
    right. right. right.
    left. split; [reflexivity | ].
    left. split; [reflexivity | ].
    exact I.
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward: In s output -> ... *)
      intros H.
      simpl in H.
      destruct H as [H | [H | [H | H]]].
      * subst. split.
        -- simpl. left. reflexivity.
        -- reflexivity.
      * subst. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- reflexivity.
      * subst. split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- reflexivity.
      * contradiction.
    + (* Backward: In s input /\ prefix ... -> In s output *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | H]]]]]].
      * subst. simpl. left. reflexivity.
      * subst. simpl in H_prefix. discriminate.
      * subst. simpl in H_prefix. discriminate.
      * subst. simpl in H_prefix. discriminate.
      * subst. simpl. right. left. reflexivity.
      * subst. simpl. left. reflexivity.
      * contradiction.
Qed.