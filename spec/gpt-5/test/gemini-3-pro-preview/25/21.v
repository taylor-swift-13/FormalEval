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

Example test_factorize_1026 : factorize_spec 1026 [2; 3; 3; 3; 19].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + repeat (apply Sorted_cons; [| constructor; try lia]). apply Sorted_nil.
    + split.
      * apply Forall_cons.
        -- unfold is_prime. split; [lia|]. intros d Hr Hd. lia.
        -- apply Forall_cons.
           ++ unfold is_prime. split; [lia|]. intros d Hr Hd. destruct Hd as [k Hk].
              assert (d = 2) by lia. subst. lia.
           ++ apply Forall_cons.
              ** unfold is_prime. split; [lia|]. intros d Hr Hd. destruct Hd as [k Hk].
                 assert (d = 2) by lia. subst. lia.
              ** apply Forall_cons.
                 --- unfold is_prime. split; [lia|]. intros d Hr Hd. destruct Hd as [k Hk].
                     assert (d = 2) by lia. subst. lia.
                 --- apply Forall_cons.
                     +++ unfold is_prime. split; [lia|]. intros d Hr Hd. destruct Hd as [k Hk].
                         assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ 
                                 d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18) as Hcases by lia.
                         repeat destruct Hcases as [Hcases | Hcases]; subst; try lia.
                     +++ apply Forall_nil.
      * simpl. reflexivity.
Qed.