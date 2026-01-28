Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition string_le (s1 s2 : string) : Prop := (String.leb s1 s2 = true).

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted string_le res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["adapplelQd"; "dapple"; "dapple"; "banana"; "aQd"; "oralQdnge"] ["aQd"; "adapplelQd"; "banana"; "dapple"; "oralQdnge"].
Proof.
  unfold unique_spec.
  split.
  - unfold string_le.
    repeat constructor; simpl; try reflexivity.
  - split.
    + repeat constructor; simpl; intuition; try discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.