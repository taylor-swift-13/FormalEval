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

Example filter_by_prefix_test_empty :
  Spec [] "john" [].
Proof.
  unfold Spec.
  split.
  - apply sub_nil.
  - intros s. split.
    + intros H. inversion H.
    + intros [H _]. inversion H.
Qed.