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

Example test_maximum : maximum_spec [0; 0; 0; 0; 0] 4 [0; 0; 0; 0].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor; apply Z.leb_le; reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [0].
      split.
      * simpl. apply Permutation_refl.
      * intros x y HInRes HInOthers.
        simpl in HInOthers. destruct HInOthers as [Heq | HFalse].
        -- subst y.
           simpl in HInRes.
           repeat (destruct HInRes as [Heq | HInRes]; [subst x; apply Z.ge_le_iff; apply Z.le_refl | ]).
           contradiction.
        -- contradiction.
Qed.