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

(* Test case: input = ["oapricot"; "apricot"], substring = "z", output = [] *)
Example problem_29_test : problem_29_spec ["oapricot"; "apricot"] "z" [].
Proof.
  unfold problem_29_spec.
  split.
  - simpl.
    trivial.
  - intros s.
    split.
    + intros H.
      inversion H.
    + intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_oap | [H_apr | H_false]].
      * subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * contradiction H_false.
Qed.