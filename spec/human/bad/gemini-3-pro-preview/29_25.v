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

(* Test case: input = ["hello"; "world"], substring = "", output = ["hello"; "world"] *)
Example problem_29_test : problem_29_spec ["hello"; "world"] "" ["hello"; "world"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence *)
    simpl.
    left. split.
    + reflexivity.
    + left. split.
      * reflexivity.
      * simpl. trivial.
  - (* Part 2: forall s *)
    intros s.
    split.
    + intros H.
      split.
      * assumption.
      * simpl. reflexivity.
    + intros [H _].
      assumption.
Qed.