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

Example test_maximum : maximum_spec [1; 0; 5; -7] 1 [5].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [1; 0; -7].
      split.
      * simpl. transitivity [1; 5; 0; -7].
        { apply perm_skip. apply perm_swap. }
        { apply perm_swap. }
      * intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [Eq | Contra]; [subst x | contradiction].
        simpl in HInOthers. destruct HInOthers as [Eq | [Eq | [Eq | Contra]]]; subst y.
        -- apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- contradiction.
Qed.