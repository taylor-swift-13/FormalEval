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

Example test_maximum : maximum_spec [0; 1; 4; 4] 2 [4; 4].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [0; 1].
      split.
      * change [0; 1; 4; 4] with ([0; 1] ++ [4; 4]).
        apply Permutation_app_comm.
      * intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [H | [H | H]]; try contradiction; subst.
        -- simpl in HInOthers. destruct HInOthers as [H | [H | H]]; try contradiction; subst.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- simpl in HInOthers. destruct HInOthers as [H | [H | H]]; try contradiction; subst.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ apply Z.le_ge. apply Z.leb_le. reflexivity.
Qed.