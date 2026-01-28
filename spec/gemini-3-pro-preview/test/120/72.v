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

Example test_maximum : maximum_spec [-1; -2; -3; 10; -5] 2 [-1; 10].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-2; -3; -5].
      split.
      * simpl.
        apply perm_skip.
        apply perm_trans with (l' := [-2; 10; -3; -5]).
        { apply perm_skip. apply perm_swap. }
        { apply perm_swap. }
      * intros x y Hx Hy.
        simpl in Hx; simpl in Hy.
        destruct Hx as [? | [? | ?]]; subst;
        destruct Hy as [? | [? | [? | ?]]]; subst; try contradiction;
        apply Z.le_ge; apply Z.leb_le; reflexivity.
Qed.