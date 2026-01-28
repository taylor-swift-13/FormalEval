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

Example test_maximum : maximum_spec [0; 1000; 0; 0] 4 [0; 0; 0; 1000].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [].
      split.
      * rewrite app_nil_r.
        apply perm_skip.
        apply perm_trans with [0; 1000; 0].
        -- apply perm_swap.
        -- apply perm_skip.
           apply perm_swap.
      * intros x y HInRes HInOthers.
        inversion HInOthers.
Qed.