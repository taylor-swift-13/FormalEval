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

Example test_maximum : maximum_spec [4; -4] 2 [-4; 4].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [-4; 4] *)
    repeat constructor.
    (* Prove -4 <= 4 *)
    apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [-4; 4]) = 2 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [].
      split.
      * (* Goal: Permutation [4; -4] ([-4; 4] ++ []) *)
        rewrite app_nil_r.
        (* The lists differ only by swapping the elements *)
        apply perm_swap.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        (* others is empty, so HInOthers is a contradiction *)
        inversion HInOthers.
Qed.