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

(* Test case: input = ["a"; "a"], substring = "a", output = ["a"] *)
Example problem_29_test : problem_29_spec ["a" ; "a"] "a" ["a"].
Proof.
  unfold problem_29_spec.
  split.
  - simpl.
    left.
    split.
    + reflexivity.
    + simpl. trivial.
  - intros s.
    split.
    + intros H.
      destruct H as [H_eq | H_false].
      * subst s.
        split.
        -- simpl. left. reflexivity.
        -- simpl. reflexivity.
      * contradiction.
    + intros [H_in H_pref].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | H3]].
      * subst s. left. reflexivity.
      * subst s. left. reflexivity.
      * contradiction.
Qed.