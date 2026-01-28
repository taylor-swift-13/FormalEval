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

Example test_maximum : maximum_spec [-2; 5; 10; 3; 8] 4 [3; 5; 8; 10].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-2].
      split.
      * apply perm_trans with ([5; 10; 3; 8] ++ [-2]).
        { apply Permutation_cons_append. }
        apply Permutation_app_tail.
        apply perm_trans with (3 :: [5; 10] ++ [8]).
        { symmetry. apply Permutation_middle. }
        simpl. apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * intros x y HInRes HInOthers.
        destruct HInOthers as [Hy | Hy]; [subst y | contradiction].
        repeat (destruct HInRes as [Hx | HInRes]; [subst x; apply Z.ge_le_iff; apply Z.leb_le; reflexivity | ]).
        contradiction.
Qed.