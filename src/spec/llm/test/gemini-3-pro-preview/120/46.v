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

Example test_maximum : maximum_spec [2; 3; 2; 2; 2] 2 [2; 3].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [2; 3] *)
    repeat constructor.
    apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [2; 3]) = 2 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [2; 2; 2].
      split.
      * (* Goal: Permutation [2; 3; 2; 2; 2] ([2; 3] ++ [2; 2; 2]) *)
        simpl. apply Permutation_refl.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        simpl in HInOthers.
        destruct HInOthers as [Hy | [Hy | [Hy | Hy]]]; try contradiction; subst y;
        simpl in HInRes;
        destruct HInRes as [Hx | [Hx | Hx]]; try contradiction; subst x;
        apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.