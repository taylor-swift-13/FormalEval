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

Example test_maximum : maximum_spec [-1; -2; -3; -4; -5] 2 [-2; -1].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [-2; -1] *)
    repeat constructor.
    + (* Prove -2 <= -1 *)
      apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [-2; -1]) = 2 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [-3; -4; -5].
      split.
      * (* Goal: Permutation [-1; -2; -3; -4; -5] ([-2; -1] ++ [-3; -4; -5]) *)
        (* This simplifies to swapping the first two elements *)
        simpl.
        apply perm_swap.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        simpl in HInRes, HInOthers.
        destruct HInRes as [H|H]; [subst|destruct H as [H|H]; [subst|contradiction]].
        -- (* x = -2 *)
           destruct HInOthers as [H|H]; [subst|destruct H as [H|H]; [subst|destruct H as [H|H]; [subst|contradiction]]].
           ++ apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
           ++ apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
           ++ apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
        -- (* x = -1 *)
           destruct HInOthers as [H|H]; [subst|destruct H as [H|H]; [subst|destruct H as [H|H]; [subst|contradiction]]].
           ++ apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
           ++ apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
           ++ apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.