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

Definition common_spec (l1 l2 out : list string) : Prop :=
  NoDup out
  /\ Sorted str_le out
  /\ forall x : string, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    ["AxY"; "IQfz"; "QTNcIWAEM"; "aPqcq"; "aPqcq"; ""; "xkxmC"] 
    [] 
    [].
Proof.
  unfold common_spec.
  split.
  - constructor.
  - split.
    + constructor.
    + intros x.
      simpl.
      intuition.
Qed.