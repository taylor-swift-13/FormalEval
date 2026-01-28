Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Import ListNotations.
Open Scope string_scope.

Fixpoint string_leb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, _ => true
  | String _ _, EmptyString => false
  | String c1 s1', String c2 s2' =>
      if Ascii.eqb c1 c2 then string_leb s1' s2'
      else Ascii.leb c1 c2
  end.

Definition string_le (s1 s2 : string) : Prop := string_leb s1 s2 = true.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted string_le res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["alQd"; "dapple"; "banana"; "aQd"; "oralQdnge"] ["aQd"; "alQd"; "banana"; "dapple"; "oralQdnge"].
Proof.
  unfold unique_spec.
  split.
  - unfold string_le.
    repeat (constructor; simpl; try reflexivity).
  - split.
    + repeat (constructor; simpl; intuition; try discriminate).
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.