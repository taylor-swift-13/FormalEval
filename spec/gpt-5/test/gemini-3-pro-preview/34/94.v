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
  unique_spec ["apple"; "banana"; "banaorangcena"; "d"] ["apple"; "banana"; "banaorangcena"; "d"].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; exact I.
  - split.
    + repeat constructor; simpl; intuition; discriminate.
    + intro x. split; auto.
Qed.