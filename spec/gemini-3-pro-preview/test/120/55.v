Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

Definition maximum_spec (arr : list Z) (k : Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  Z.of_nat (length res) = k /\
  exists (others : list Z),
    Permutation arr (res ++ others) /\
    (forall x y, In x res -> In y others -> x >= y).

Example test_maximum : maximum_spec [-4; -3; 1] 1 [1].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [-4; -3].
      split.
      * simpl. apply perm_trans with (l' := [-4; 1; -3]).
        { apply perm_skip. apply perm_swap. }
        { apply perm_swap. }
      * intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [Hx | HFalse]; [| contradiction].
        rewrite <- Hx.
        simpl in HInOthers. destruct HInOthers as [Hy | [Hy | HFalse]].
        { rewrite <- Hy. apply Z.le_ge. apply Z.leb_le. reflexivity. }
        { rewrite <- Hy. apply Z.le_ge. apply Z.leb_le. reflexivity. }
        { contradiction. }
Qed.