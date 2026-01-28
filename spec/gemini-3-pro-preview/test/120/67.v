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

Example test_maximum : maximum_spec [-2; -3; -3; 10; -5] 4 [-3; -3; -2; 10].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [-3; -3; -2; 10] *)
    repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [-3; -3; -2; 10]) = 4 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [-5].
      split.
      * (* Goal: Permutation [-2; -3; -3; 10; -5] ([-3; -3; -2; 10] ++ [-5]) *)
        simpl.
        (* We need to show Permutation [-2; -3; -3; 10; -5] [-3; -3; -2; 10; -5] *)
        apply Permutation_trans with (l' := [-3; -2; -3; 10; -5]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        simpl in HInOthers.
        destruct HInOthers as [EqY | []].
        rewrite <- EqY.
        simpl in HInRes.
        destruct HInRes as [EqX | [EqX | [EqX | [EqX | []]]]];
          rewrite <- EqX; apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.