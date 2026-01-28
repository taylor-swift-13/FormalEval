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

Example test_maximum : maximum_spec [5; 2; 1] 1 [5].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [2; 1].
      split.
      * simpl. apply Permutation_refl.
      * intros x y Hx Hy.
        destruct Hx as [Hx | Hx]; [subst x | contradiction].
        destruct Hy as [Hy | Hy]; [subst y |].
        -- apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- destruct Hy as [Hy | Hy]; [subst y | contradiction].
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
Qed.