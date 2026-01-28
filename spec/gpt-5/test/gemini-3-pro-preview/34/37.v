Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition unique_spec (l : list string) (res : list string) : Prop :=
  Sorted (fun s1 s2 => String.leb s1 s2 = true) res /\
  NoDup res /\
  forall x : string, In x res <-> In x l.

Example test_unique_spec : 
  unique_spec ["apple"; "banana"; "lQd"; "llQd"; "orange"] ["apple"; "banana"; "lQd"; "llQd"; "orange"].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor.
  - split.
    + repeat constructor; simpl; intuition; discriminate.
    + intro x. split; auto.
Qed.