Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example problem_29_test_case : problem_29_spec ["a"; "a"] "a" ["a"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_match. apply sub_nil.
  - intros s; split.
    + intros H. destruct H as [Hs | Hnil].
      * subst s. split.
        { left; reflexivity. }
        { simpl. reflexivity. }
      * inversion Hnil.
    + intros [Hin Hpref]. destruct Hin as [Hs | [Hs2 | HinNil]].
      * subst s. left. reflexivity.
      * subst s. left. reflexivity.
      * inversion HinNil.
Qed.