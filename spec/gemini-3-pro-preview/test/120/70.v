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

Example test_maximum : maximum_spec [-1; -2; -3; 10; -5] 3 [-2; -1; 10].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le; reflexivity.
    + apply Z.leb_le; reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-3; -5].
      split.
      * simpl.
        apply Permutation_trans with (l' := [-2; -1; -3; 10; -5]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        apply Permutation_trans with (l' := [10; -3; -5]).
        { apply perm_swap. }
        apply Permutation_refl.
      * intros x y Hx Hy.
        simpl in Hx, Hy.
        destruct Hx as [Hx | [Hx | [Hx | Hx]]]; subst.
        -- destruct Hy as [Hy | [Hy | Hy]]; subst; try contradiction.
           ++ apply Z.le_ge; apply Z.leb_le; reflexivity.
           ++ apply Z.le_ge; apply Z.leb_le; reflexivity.
        -- destruct Hy as [Hy | [Hy | Hy]]; subst; try contradiction.
           ++ apply Z.le_ge; apply Z.leb_le; reflexivity.
           ++ apply Z.le_ge; apply Z.leb_le; reflexivity.
        -- destruct Hy as [Hy | [Hy | Hy]]; subst; try contradiction.
           ++ apply Z.le_ge; apply Z.leb_le; reflexivity.
           ++ apply Z.le_ge; apply Z.leb_le; reflexivity.
        -- contradiction.
Qed.