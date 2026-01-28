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

Definition common_spec (l1 l2 res : list string) : Prop :=
  Sorted string_le res /\
  NoDup res /\
  (forall x : string, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    ["QoHVx"; "Pqo"; "PqvvtmNe"; "Pqo"; "XNNCdHcXOu"; "XC"; "CXAPmEz"; ""]
    ["QoHVx"; "Pqo"; "PqvvtmNe"; "Pqo"; "XNNCdHcXOu"; "XC"; "CXAPmEz"; ""]
    [""; "CXAPmEz"; "Pqo"; "PqvvtmNe"; "QoHVx"; "XC"; "XNNCdHcXOu"].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    unfold string_le.
    repeat constructor; simpl; try tauto.
  - split.
    + (* NoDup *)
      repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [discriminate | ]); contradiction.
    + (* Equivalence *)
      intros x. split.
      * (* -> *)
        intro H. simpl in H.
        repeat (destruct H as [H|H]; [subst; simpl; tauto | ]); contradiction.
      * (* <- *)
        intros [H1 H2]. simpl in H1.
        repeat (destruct H1 as [H1|H1]; [
          subst; simpl; tauto
        | ]); contradiction.
Qed.