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

Example test_maximum : maximum_spec [-2; -3; -4; -5] 2 [-3; -2].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-4; -5].
      split.
      * simpl. apply perm_swap.
      * intros x y HInRes HInOthers.
        simpl in HInRes, HInOthers.
        destruct HInRes as [H | [H | H]]; subst.
        -- destruct HInOthers as [H | [H | H]]; subst.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ contradiction.
        -- destruct HInOthers as [H | [H | H]]; subst.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ contradiction.
        -- contradiction.
Qed.