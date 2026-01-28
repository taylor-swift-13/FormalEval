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

Example test_maximum : maximum_spec [1; 1] 1 [1].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [1] *)
    repeat constructor.
  - split.
    + (* Goal: Z.of_nat (length [1]) = 1 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [1].
      split.
      * (* Goal: Permutation [1; 1] ([1] ++ [1]) *)
        simpl. apply Permutation_refl.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [HeqX | HFalseX]; [subst x | contradiction].
        simpl in HInOthers. destruct HInOthers as [HeqY | HFalseY]; [subst y | contradiction].
        apply Z.ge_le_iff. apply Z.le_refl.
Qed.