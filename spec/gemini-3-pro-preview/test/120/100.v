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

Example test_maximum : maximum_spec [3; 4; 5] 3 [3; 4; 5].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [3; 4; 5] *)
    repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [3; 4; 5]) = 3 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [].
      split.
      * (* Goal: Permutation [3; 4; 5] ([3; 4; 5] ++ []) *)
        rewrite app_nil_r.
        apply Permutation_refl.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        inversion HInOthers.
Qed.