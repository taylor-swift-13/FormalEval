Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

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

Example test_case : problem_29_spec ["x"; "john"] "a" [].
Proof.
  unfold problem_29_spec.
  split.
  - (* Prove is_subsequence [] ["x"; "john"] *)
    simpl.
    exact I.
  - (* Prove forall s, In s [] <-> (In s ["x"; "john"] /\ String.prefix "a" s = true) *)
    intro s.
    split.
    + intro H.
      contradiction. (* In s [] is always false *)
    + intro H.
      destruct H as [Hin Hprefix].
      contradiction. (* Left side is always false, so implication holds *)
Qed.