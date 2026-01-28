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

Example test_maximum : maximum_spec [1; 2; 3] 2 [2; 3].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [2; 3] *)
    repeat constructor.
    (* Prove 2 <= 3 *)
    apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [2; 3]) = 2 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [1].
      split.
      * (* Goal: Permutation [1; 2; 3] ([2; 3] ++ [1]) *)
        (* [2; 3] ++ [1] simplifies to [2; 3; 1] *)
        simpl.
        (* Transform [1; 2; 3] -> [2; 1; 3] -> [2; 3; 1] *)
        apply Permutation_trans with (l' := [2; 1; 3]).
        { apply perm_swap. }
        { apply perm_skip. apply perm_swap. }
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        (* others is [1] *)
        inversion HInOthers as [H1 | H1]; subst.
        -- (* y = 1 *)
           inversion HInRes as [H2 | H2]; subst.
           ++ (* x = 2 *)
              apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
           ++ (* x is in [3] *)
              inversion H2 as [H3 | H3]; subst.
              ** (* x = 3 *)
                 apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
              ** (* x in [] *)
                 inversion H3.
        -- (* y in [] *)
           inversion H1.
Qed.