Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted string_le res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["apple"; "d"; "orange"] ["apple"; "d"; "orange"].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; auto.
  - split.
    + repeat constructor; simpl; intuition; discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto.
      * repeat destruct H as [H|H]; subst; auto.
Qed.