Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition str_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted str_le res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec 
    ["adapplelQd"; "dapple"; "davcvAoc"; "banana"; "aQd"; "oralQdnge"] 
    ["aQd"; "adapplelQd"; "banana"; "dapple"; "davcvAoc"; "oralQdnge"].
Proof.
  unfold unique_spec.
  split.
  - unfold str_le.
    repeat constructor; simpl; trivial.
  - split.
    + repeat constructor; simpl; intuition; discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.