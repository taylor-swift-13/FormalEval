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

Example test_case_empty_output :
  let input := ["hah"; "hah"] in
  let substring := "a" in
  let output := [] in
  problem_29_spec input substring output.
Proof.
  unfold problem_29_spec.
  split.
  - simpl. trivial.
  - intros s.
    split; intros H.
    + inversion H.
    + destruct H as [Hin Hpre].
      simpl in Hin.
      destruct Hin as [Heq | [Heq | Hfalse]].
      * subst. simpl in Hpre. discriminate Hpre.
      * subst. simpl in Hpre. discriminate Hpre.
      * contradiction.
Qed.