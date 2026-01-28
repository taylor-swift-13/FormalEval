Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition le_string (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted le_string res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["a"; "b"; "b"; "h"; "c"; "c"; "c"; "d"; "d"; "d"; "e"; "e"; "e"; "f"; "f"; "f"; "g"; "g"; "g"] ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"].
Proof.
  unfold unique_spec.
  split.
  - unfold le_string.
    repeat constructor; simpl; try (vm_compute; congruence).
  - split.
    + repeat constructor; simpl; intuition; discriminate.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.