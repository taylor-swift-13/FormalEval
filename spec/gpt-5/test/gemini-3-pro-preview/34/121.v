Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition str_le (s1 s2 : string) : Prop := (String.leb s1 s2) = true.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted str_le res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["e"; "h"; ""; "e"; "b"; "pExeV"; "j"; "e"] [""; "b"; "e"; "h"; "j"; "pExeV"].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted str_le res *)
    unfold str_le.
    repeat constructor; simpl; reflexivity.
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