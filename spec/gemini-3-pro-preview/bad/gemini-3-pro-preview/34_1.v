Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

Definition unique_spec (l : list Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  NoDup res /\
  (forall x : Z, In x res <-> In x l).

Example test_unique : unique_spec [5; 3; 5; 2; 3; 3; 9; 0; 123] [0; 2; 3; 5; 9; 123].
Proof.
  unfold unique_spec.
  repeat split.
  - (* Prove Sorted *)
    repeat constructor.
    (* Solve integer inequalities Z.le x y *)
    all: try (apply Z.leb_le; reflexivity).
  - (* Prove NoDup *)
    repeat constructor.
    (* Solve non-membership ~ In x l *)
    all: intro H; simpl in H; tauto.
  - (* Prove Equivalence *)
    intro z.
    simpl.
    tauto.
Qed.