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

Example test_maximum : maximum_spec [1; 1; 1] 1 [1].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [1; 1].
      split.
      * simpl. apply Permutation_refl.
      * intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [HeqX | HFalse]; [subst x | contradiction].
        simpl in HInOthers. destruct HInOthers as [HeqY | [HeqY | HFalse]]; try contradiction; subst y; apply Z.ge_le_iff; apply Z.le_refl.
Qed.