Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.

Import ListNotations.
Open Scope string_scope.

Definition common_spec (l1 l2 out : list string) : Prop :=
  NoDup out
  /\ Sorted (fun s1 s2 => String.compare s1 s2 <> Gt) out
  /\ forall x : string, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    ["SfYzsI"; "CXAPmEz"; "D"; "SfYzsI"] 
    [] 
    [].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    constructor.
  - split.
    + (* Prove Sorted out *)
      constructor.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      intuition.
Qed.