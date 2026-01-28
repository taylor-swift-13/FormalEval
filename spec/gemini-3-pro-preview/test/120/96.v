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

Example test_maximum : maximum_spec [5; 2; 0] 2 [2; 5].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [0].
      split.
      * simpl. apply perm_swap.
      * intros x y HInRes HInOthers.
        destruct HInOthers as [Hy | HFalse].
        -- subst y.
           destruct HInRes as [Hx | [Hx | HFalse]].
           ++ subst x. apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
           ++ subst x. apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
           ++ contradiction.
        -- contradiction.
Qed.