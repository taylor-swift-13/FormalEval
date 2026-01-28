Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  2 <= p /\ forall d, 2 <= d < p -> ~ Z.divide d p.

Fixpoint list_prod (l : list Z) : Z :=
  match l with
  | nil => 1
  | x :: xs => x * list_prod xs
  end.

Definition factorize_spec (n : Z) (fact : list Z) : Prop :=
  1 <= n /\ Sorted Z.le fact /\ Forall is_prime fact /\ list_prod fact = n.

Example test_factorize_1028 : factorize_spec 1028 [2; 2; 257].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons; lia.
      * apply HdRel_cons; lia.
    + split.
      * apply Forall_cons.
        -- unfold is_prime; split.
           ++ lia.
           ++ intros d Hrange Hdiv; lia.
        -- apply Forall_cons.
           ++ unfold is_prime; split.
              ** lia.
              ** intros d Hrange Hdiv; lia.
           ++ apply Forall_cons.
              ** unfold is_prime; split.
                 --- lia.
                 --- intros d Hrange [k Hk].
                     assert (d * k = 257) by lia.
                     assert (d < 17 \/ k < 17) as [Hsmall|Hsmall].
                     { destruct (Z.lt_ge_cases d 17); [left; lia|right].
                       destruct (Z.lt_ge_cases k 17); [lia|].
                       assert (17 * 17 <= d * k) by (apply Z.mul_le_mono_nonneg; lia).
                       lia. }
                     { assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16) as Hcases by lia.
                       repeat (destruct Hcases as [Hcases|Hcases]; [subst; lia|]).
                       subst; lia. }
                     { assert (k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16) as Hcases.
                       { destruct (Z.le_gt_cases k 1); [assert (d*k <= 256*1) by (apply Z.mul_le_mono_nonneg; lia); lia|lia]. }
                       repeat (destruct Hcases as [Hcases|Hcases]; [subst; lia|]).
                       subst; lia. }
              ** apply Forall_nil.
      * simpl. reflexivity.
Qed.