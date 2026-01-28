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

Example test_maximum : maximum_spec [2; 2; 2; 2; 2] 2 [2; 2].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [2; 2; 2].
      split.
      * simpl. apply Permutation_refl.
      * intros x y Hx Hy.
        simpl in Hx. destruct Hx as [? | [? | ?]]; subst;
        simpl in Hy; destruct Hy as [? | [? | [? | ?]]]; subst; try contradiction;
        apply Z.ge_le_iff; apply Z.le_refl.
Qed.