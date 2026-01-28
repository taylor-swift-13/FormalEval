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

Example test_maximum : maximum_spec [1; 2; 2; 3; 4; 5] 3 [3; 4; 5].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le; reflexivity.
    + apply Z.leb_le; reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [1; 2; 2].
      split.
      * change [1; 2; 2; 3; 4; 5] with ([1; 2; 2] ++ [3; 4; 5]).
        apply Permutation_app_comm.
      * intros x y Hx Hy.
        repeat destruct Hx as [<- | Hx];
        repeat destruct Hy as [<- | Hy];
        try contradiction;
        apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.