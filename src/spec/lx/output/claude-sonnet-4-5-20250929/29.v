Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : is_subsequence [] []
  | sub_cons_hd : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition Spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Lemma is_subsequence_nil_left : forall {A : Type} (l : list A),
  is_subsequence [] l.
Proof.
  intros A l.
  induction l as [|h t IH].
  - apply sub_nil.
  - apply sub_cons_tl.
    exact IH.
Qed.

Example test_filter_by_prefix_empty :
  Spec [] "john" [].
Proof.
  unfold Spec.
  split.
  - apply sub_nil.
  - intro s.
    split.
    + intro H.
      contradiction.
    + intro H.
      destruct H as [H1 H2].
      contradiction.
Qed.