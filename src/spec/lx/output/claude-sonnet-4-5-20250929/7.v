Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if sub =? EmptyString then true else false
  | String _ rest =>
      if String.prefix s sub then true
      else contains_substring rest sub
  end.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : is_subsequence [] []
  | sub_cons_hd : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition spec_filter_by_pre : Prop:= True.

Definition spec_filter_by_substring (input output : list string) (sub : string) : Prop:=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ contains_substring s sub = true)).

Lemma is_subsequence_nil_left : forall {A : Type} (l : list A),
  is_subsequence [] l.
Proof.
  intros A l.
  induction l as [|h t IH].
  - apply sub_nil.
  - apply sub_cons_tl.
    exact IH.
Qed.

Example test_filter_by_substring_empty :
  spec_filter_by_substring [] [] "john".
Proof.
  unfold spec_filter_by_substring.
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