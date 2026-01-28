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

Example test_unique_spec : 
  unique_spec [1; 2; 2; 3; 4; 4; 5; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 7] [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; try lia.
  - split.
    + repeat constructor; simpl; intuition; try lia.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 30.
      * repeat destruct H as [H|H]; subst; auto 30.
Qed.