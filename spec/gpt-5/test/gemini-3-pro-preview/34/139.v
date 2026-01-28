Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope string_scope.

Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      match (nat_of_ascii c1 ?= nat_of_ascii c2)%nat with
      | Lt => True
      | Gt => False
      | Eq => string_le s1' s2'
      end
  end.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted string_le res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["e"; "jc"; "h"; ""; "e"; "b"; "pExeV"; "j"] [""; "b"; "e"; "h"; "j"; "jc"; "pExeV"].
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