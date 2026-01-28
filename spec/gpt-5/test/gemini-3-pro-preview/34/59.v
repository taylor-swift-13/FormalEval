Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted (fun s1 s2 => String.leb s1 s2 = true) res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["apple"; "banana"; "lQd"; "oralQdnge"; "oralQdnge"] ["apple"; "banana"; "lQd"; "oralQdnge"].
Proof.
  unfold unique_spec.
  split.
  - (* Prove Sorted *)
    repeat constructor; simpl; reflexivity.
  - split.
    + (* Prove NoDup *)
      repeat constructor; simpl; intuition; discriminate.
    + (* Prove In x res <-> In x l *)
      intro x.
      simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H|H]; subst; auto 20.
      * (* <- direction *)
        repeat destruct H as [H|H]; subst; auto 20.
Qed.