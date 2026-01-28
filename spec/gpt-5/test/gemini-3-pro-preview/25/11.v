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

Example test_factorize_28 : factorize_spec 28 [2; 2; 7].
Proof.
  unfold factorize_spec.
  split.
  - (* 1 <= 28 *)
    lia.
  - split.
    + (* Sorted *)
      apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
    + split.
      * (* Forall is_prime *)
        apply Forall_cons.
        -- (* 2 *)
           unfold is_prime. split. lia. intros d Hrange Hdiv. lia.
        -- apply Forall_cons.
           ++ (* 2 *)
              unfold is_prime. split. lia. intros d Hrange Hdiv. lia.
           ++ apply Forall_cons.
              ** (* 7 *)
                 unfold is_prime. split. lia.
                 intros d [Hge Hlt] [k Hk].
                 assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
                 destruct H as [-> | [-> | [-> | [-> | ->]]]].
                 --- assert (3 < k < 4) by lia. lia.
                 --- assert (2 < k < 3) by lia. lia.
                 --- assert (1 < k < 2) by lia. lia.
                 --- assert (1 < k < 2) by lia. lia.
                 --- assert (1 < k < 2) by lia. lia.
              ** apply Forall_nil.
      * (* Product *)
        simpl. reflexivity.
Qed.