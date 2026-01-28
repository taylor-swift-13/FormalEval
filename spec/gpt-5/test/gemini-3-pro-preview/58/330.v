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
    ["QoHVx"; "Pqo"; "PqvvtmNe"; "Pqo"; "D"; "XNNCdHcXOu"; "XC"; "CXAPmEz"; ""] 
    ["QoHVx"; "Pqo"; "PqvvtmNe"; "Pqo"; "D"; "XNNCdHcXOu"; "XC"; "CXAPmEz"; ""] 
    [""; "CXAPmEz"; "D"; "Pqo"; "PqvvtmNe"; "QoHVx"; "XC"; "XNNCdHcXOu"].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    repeat constructor; simpl; intuition; discriminate.
  - split.
    + (* Prove Sorted string_le out *)
      repeat constructor; unfold string_le; simpl; trivial.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      intuition; subst; simpl; intuition; try discriminate.
Qed.