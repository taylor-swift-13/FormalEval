Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

Definition le_string (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition common_spec (l1 l2 res : list string) : Prop :=
  Sorted le_string res /\
  NoDup res /\
  (forall x : string, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    ["SfYzsI"; "CXAPmEz"; "D"; "SfYzsI"] 
    ["QoHVx"; "Pqo"; "Pqo"; "D"; "XNNCdHcXOu"; "XC"; "CXAPmEz"; ""] 
    ["CXAPmEz"; "D"].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    repeat constructor.
    simpl. trivial.
  - split.
    + (* NoDup *)
      repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [ discriminate | ]); contradiction.
    + (* Equivalence *)
      intros x. split.
      * (* -> *)
        intro H. simpl in H.
        repeat (destruct H as [H|H]; [subst; simpl; tauto | ]); contradiction.
      * (* <- *)
        intros [H1 H2].
        repeat (destruct H1 as [H1|H1]; subst; [
          simpl in H2;
          repeat (destruct H2 as [H2|H2]; [ try discriminate; simpl; tauto | ]);
          try contradiction
        | ]); try contradiction.
Qed.