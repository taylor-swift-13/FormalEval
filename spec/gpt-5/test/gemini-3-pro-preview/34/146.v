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
  unique_spec [999999999999999999999999999999999; 5555555555555555555555; 1; -999999999999999999999999999999999; -5555555555555555555555; -5555555555555555555554] 
              [-999999999999999999999999999999999; -5555555555555555555555; -5555555555555555555554; 1; 5555555555555555555555; 999999999999999999999999999999999].
Proof.
  unfold unique_spec.
  split.
  - repeat constructor; simpl; try lia.
  - split.
    + repeat constructor; simpl; intuition; try lia.
    + intro x.
      simpl.
      split; intro H.
      * repeat destruct H as [H|H]; subst; auto 20.
      * repeat destruct H as [H|H]; subst; auto 20.
Qed.