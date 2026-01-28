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

(* Test case: input = ["apple"; "orange"; "banana"], substring = "b", output = ["banana"] *)
Example problem_29_test : problem_29_spec ["apple"; "orange"; "banana"] "b" ["banana"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    right. right. left.
    split; [reflexivity | simpl; trivial].
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward: In s output -> ... *)
      intros H.
      destruct H as [H_eq | H_false].
      * subst s.
        split.
        -- simpl. auto 6. (* In "banana" ... *)
        -- simpl. reflexivity.
      * contradiction.
    + (* Backward: In s input /\ prefix ... -> In s output *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_apple | [H_orange | [H_banana | H_false]]].
      * (* Case 1: s = "apple" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 2: s = "orange" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 3: s = "banana" *)
        subst s.
        left. reflexivity.
      * (* Case 4: s in [] *)
        contradiction H_false.
Qed.