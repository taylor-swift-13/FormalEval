Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition unique_spec (l : list Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  NoDup res /\
  forall x : Z, In x res <-> In x l.

Example test_unique : unique_spec [5; 3; 5; 2; 3; 3; 9; 0; 123] [0; 2; 3; 5; 9; 123].
Proof.
  unfold unique_spec.
  split.
  - (* Part 1: Sorted Z.le res *)
    repeat constructor.
    (* The constructor tactic generates subgoals for Z.le constraints *)
    all: simpl; try lia.
  - split.
    + (* Part 2: NoDup res *)
      repeat constructor.
      (* The constructor tactic generates subgoals for ~ In x l *)
      all: simpl; intuition discriminate.
    + (* Part 3: In x res <-> In x l *)
      intro x; simpl.
      split; intro H.
      * (* -> direction *)
        repeat destruct H as [H | H]; subst; tauto.
      * (* <- direction *)
        repeat destruct H as [H | H]; subst; tauto.
Qed.