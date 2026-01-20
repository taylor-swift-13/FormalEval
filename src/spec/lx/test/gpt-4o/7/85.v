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

Definition spec_filter_by_pre : Prop := True.

Definition spec_filter_by_substring (input output : list string) (sub : string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ contains_substring s sub = true)).

Example filter_by_substring_test_empty :
  spec_filter_by_substring [] [] "nabc(d)e".
Proof.
  unfold spec_filter_by_substring.
  split.
  - apply sub_nil.
  - intros s. split.
    + intros H. inversion H.
    + intros [H1 H2]. inversion H1.
Qed.