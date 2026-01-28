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

Example test_maximum : maximum_spec [1; 4] 1 [4].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [1].
      split.
      * simpl. apply perm_swap.
      * intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [Hx | HFalse].
        2: contradiction.
        simpl in HInOthers. destruct HInOthers as [Hy | HFalse].
        2: contradiction.
        subst.
        apply Z.le_ge.
        apply Z.leb_le.
        reflexivity.
Qed.