Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted (fun s1 s2 => String.compare s1 s2 <> Gt) res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["apple"; "banana"; "lQd"; "oralQdnge"] ["apple"; "banana"; "lQd"; "oralQdnge"].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; intro H; discriminate.
  - split.
    + repeat constructor; simpl; intuition; try discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.