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

Example test_factorize_29 : factorize_spec 29 [29].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + split.
      * apply Forall_cons.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hrange Hdiv.
              destruct Hdiv as [k Hk].
              assert (Heq: 29 = k * d) by lia.
              assert (Hbounds: d <= 5 \/ k <= 4).
              {
                destruct (Z_le_gt_dec d 5); [left; lia|].
                right.
                destruct (Z_le_gt_dec k 4); [lia|].
                assert (Hmul: k * d >= 5 * 6).
                { apply Z.mul_le_mono_nonneg; lia. }
                lia.
              }
              destruct Hbounds as [Hd | Hk_small].
              ** assert (Hcases: d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
                 destruct Hcases as [H|H|H|H]; subst d; lia.
              ** assert (Hcases: k = 2 \/ k = 3 \/ k = 4) by lia.
                 destruct Hcases as [H|H|H]; subst k; lia.
        -- apply Forall_nil.
      * simpl. reflexivity.
Qed.