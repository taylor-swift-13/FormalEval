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

Example test_maximum : maximum_spec [-1000; 0; 1000] 1 [1000].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [-1000; 0].
      split.
      * apply perm_trans with (l' := [-1000; 1000; 0]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * intros x y Hx Hy.
        inversion Hx; subst.
        -- inversion Hy; subst.
           ++ apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
           ++ inversion H; subst.
              ** apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
              ** inversion H0.
        -- inversion H.
Qed.