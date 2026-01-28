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

(* Test case: input = ["zz"; "z"], substring = "z", output = ["zz"; "z"] *)
Example problem_29_test : problem_29_spec ["zz"; "z"] "z" ["zz"; "z"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    left. split.
    + reflexivity.
    + left. split.
      * reflexivity.
      * trivial.
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward *)
      intros H.
      simpl in H.
      destruct H as [H_zz | [H_z | H_false]].
      * subst s.
        split.
        -- simpl. left. reflexivity.
        -- simpl. reflexivity.
      * subst s.
        split.
        -- simpl. right. left. reflexivity.
        -- simpl. reflexivity.
      * contradiction.
    + (* Backward *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_zz | [H_z | H_false]].
      * subst s.
        simpl. left. reflexivity.
      * subst s.
        simpl. right. left. reflexivity.
      * contradiction.
Qed.