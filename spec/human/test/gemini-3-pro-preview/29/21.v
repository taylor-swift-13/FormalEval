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

(* Test case: input = ["aa"; "a"], substring = "a", output = ["aa"; "a"] *)
Example problem_29_test : problem_29_spec ["aa" ; "a"] "a" ["aa" ; "a"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    left. split; [reflexivity |].
    left. split; [reflexivity |].
    trivial.
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward: In s output -> ... *)
      intros H.
      split.
      * assumption.
      * destruct H as [H_aa | [H_a | H_false]].
        -- subst s. reflexivity.
        -- subst s. reflexivity.
        -- contradiction.
    + (* Backward: In s input /\ prefix ... -> In s output *)
      intros [H_in H_prefix].
      assumption.
Qed.