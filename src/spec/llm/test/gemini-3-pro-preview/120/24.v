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

Example test_maximum : maximum_spec [1; 4; 4] 1 [4].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [4] *)
    repeat constructor.
  - split.
    + (* Goal: Z.of_nat (length [4]) = 1 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [1; 4].
      split.
      * (* Goal: Permutation [1; 4; 4] ([4] ++ [1; 4]) *)
        simpl.
        (* Goal: Permutation [1; 4; 4] [4; 1; 4] *)
        (* The lists differ only by swapping the first two elements (1 and 4) *)
        apply perm_swap.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        (* x must be 4 *)
        simpl in HInRes. destruct HInRes as [Hx | HFalse]; [subst x | contradiction].
        (* y must be 1 or 4 *)
        simpl in HInOthers. destruct HInOthers as [Hy1 | [Hy2 | HFalse]].
        -- (* y = 1, prove 4 >= 1 *)
           subst y.
           apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- (* y = 4, prove 4 >= 4 *)
           subst y.
           apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- contradiction.
Qed.