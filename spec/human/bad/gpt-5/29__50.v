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

Example problem_29_test_case : problem_29_spec ["world"; "hello"; "world"] "" ["world"; "hello"; "world"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros s; split.
    + intro Hin. split.
      * exact Hin.
      * simpl. reflexivity.
    + intros [Hin Hpref]. exact Hin.
Qed.