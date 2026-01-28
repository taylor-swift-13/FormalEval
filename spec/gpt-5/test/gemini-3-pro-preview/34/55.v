Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

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
  unique_spec ["a"; "b"; "b"; "c"; "dd"; "d"] ["a"; "b"; "c"; "d"; "dd"].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted string_le res *)
    repeat constructor; simpl; auto.
  - split.
    + (* Prove NoDup res *)
      repeat constructor; simpl; intuition; try discriminate.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; auto 20.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto 20.
Qed.