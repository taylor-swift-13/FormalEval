Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example test_filter_by_prefix_1 :
  problem_29_spec [EmptyString; ""%string] "a"%string [].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_nil.
  - intro s.
    split.
    + intro H.
      simpl in H.
      destruct H.
    + intro H.
      destruct H as [Hin Hprefix].
      simpl in Hin.
      destruct Hin as [Hs | [Hs | Hfalse]].
      * subst s.
        simpl in Hprefix.
        inversion Hprefix.
      * subst s.
        simpl in Hprefix.
        inversion Hprefix.
      * contradiction.
Qed.