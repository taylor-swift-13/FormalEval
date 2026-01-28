Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

Definition str_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition common_spec (l1 l2 res : list string) : Prop :=
  Sorted str_le res /\
  NoDup res /\
  (forall x : string, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    ["SfYzsI"; "CXAPmEz"; "D"; "SfYzsI"] 
    [] 
    [].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    constructor.
  - split.
    + (* NoDup *)
      constructor.
    + (* Equivalence *)
      intros x. split.
      * (* -> *)
        intro H. inversion H.
      * (* <- *)
        intros [H1 H2]. inversion H2.
Qed.