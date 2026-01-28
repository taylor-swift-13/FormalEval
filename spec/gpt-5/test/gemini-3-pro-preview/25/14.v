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

Example test_factorize_33 : factorize_spec 33 [3; 11].
Proof.
  unfold factorize_spec.
  split.
  - (* 1 <= 33 *)
    lia.
  - split.
    + (* Sorted Z.le [3; 11] *)
      apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * apply HdRel_cons. simpl. lia.
    + split.
      * (* Forall is_prime [3; 11] *)
        apply Forall_cons.
        -- (* is_prime 3 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d Hrange Hdiv.
              destruct Hdiv as [z Hz].
              assert (d = 2) by lia. subst.
              (* 3 = z * 2 *)
              assert (z <= 1 \/ z >= 2) by lia.
              destruct H; [ assert (z * 2 <= 2) by lia | assert (z * 2 >= 4) by lia ]; lia.
        -- apply Forall_cons.
           ++ (* is_prime 11 *)
              unfold is_prime. split.
              ** lia.
              ** intros d Hrange Hdiv.
                 destruct Hdiv as [z Hz].
                 (* Brute force check for d in 2..10 *)
                 assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) by lia.
                 destruct H as [?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]; subst.
                 --- (* d=2 *) assert (z <= 5 \/ z >= 6) by lia. destruct H; [assert (z*2 <= 10) by lia | assert (z*2 >= 12) by lia]; lia.
                 --- (* d=3 *) assert (z <= 3 \/ z >= 4) by lia. destruct H; [assert (z*3 <= 9) by lia | assert (z*3 >= 12) by lia]; lia.
                 --- (* d=4 *) assert (z <= 2 \/ z >= 3) by lia. destruct H; [assert (z*4 <= 8) by lia | assert (z*4 >= 12) by lia]; lia.
                 --- (* d=5 *) assert (z <= 2 \/ z >= 3) by lia. destruct H; [assert (z*5 <= 10) by lia | assert (z*5 >= 15) by lia]; lia.
                 --- (* d=6 *) assert (z <= 1 \/ z >= 2) by lia. destruct H; [assert (z*6 <= 6) by lia | assert (z*6 >= 12) by lia]; lia.
                 --- (* d=7 *) assert (z <= 1 \/ z >= 2) by lia. destruct H; [assert (z*7 <= 7) by lia | assert (z*7 >= 14) by lia]; lia.
                 --- (* d=8 *) assert (z <= 1 \/ z >= 2) by lia. destruct H; [assert (z*8 <= 8) by lia | assert (z*8 >= 16) by lia]; lia.
                 --- (* d=9 *) assert (z <= 1 \/ z >= 2) by lia. destruct H; [assert (z*9 <= 9) by lia | assert (z*9 >= 18) by lia]; lia.
                 --- (* d=10 *) assert (z <= 1 \/ z >= 2) by lia. destruct H; [assert (z*10 <= 10) by lia | assert (z*10 >= 20) by lia]; lia.
           ++ apply Forall_nil.
      * (* list_prod [3; 11] = 33 *)
        simpl. reflexivity.
Qed.