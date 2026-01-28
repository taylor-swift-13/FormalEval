Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.

Import ListNotations.
Open Scope string_scope.

Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition common_spec (l1 l2 out : list string) : Prop :=
  NoDup out
  /\ Sorted string_le out
  /\ forall x : string, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    ["SfYzsI"; "CXAPmEz"; "D"; "SfYzsI"] 
    ["QoHVx"; "Pqo"; "Pqo"; "D"; "XNNCdHcXOu"; "XC"; "CXAPmEz"; ""] 
    ["CXAPmEz"; "D"].
Proof.
  unfold common_spec.
  split.
  - repeat constructor; simpl; intuition; discriminate.
  - split.
    + unfold string_le. repeat constructor.
    + intros x.
      simpl.
      intuition; subst; simpl in *;
      repeat (match goal with | [ H : _ \/ _ |- _ ] => destruct H end);
      try congruence; auto.
Qed.