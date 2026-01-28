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

Example test_factorize_3249 : factorize_spec 3249 [3; 3; 19; 19].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || (apply HdRel_cons; lia)).
    + split.
      * apply Forall_cons.
        -- unfold is_prime. split. lia.
           intros d Hrange Hdiv. destruct Hdiv as [k Hk].
           assert (d = 2) by lia. subst. lia.
        -- apply Forall_cons.
           ++ unfold is_prime. split. lia.
              intros d Hrange Hdiv. destruct Hdiv as [k Hk].
              assert (d = 2) by lia. subst. lia.
           ++ apply Forall_cons.
              ** unfold is_prime. split. lia.
                 intros d Hrange Hdiv. destruct Hdiv as [k Hk].
                 assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18) by lia.
                 repeat destruct H as [H|H]; subst; lia.
              ** apply Forall_cons.
                 --- unfold is_prime. split. lia.
                     intros d Hrange Hdiv. destruct Hdiv as [k Hk].
                     assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18) by lia.
                     repeat destruct H as [H|H]; subst; lia.
                 --- apply Forall_nil.
      * simpl. reflexivity.
Qed.