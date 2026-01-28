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

Example test_factorize_132 : factorize_spec 132 [2; 2; 3; 11].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
    + split.
      * apply Forall_cons.
        -- unfold is_prime. split. lia. intros d H1 [k H2]. lia.
        -- apply Forall_cons.
           ++ unfold is_prime. split. lia. intros d H1 [k H2]. lia.
           ++ apply Forall_cons.
              ** unfold is_prime. split. lia. intros d H1 [k H2].
                 assert (d = 2) by lia. subst. lia.
              ** apply Forall_cons.
                 --- unfold is_prime. split. lia. intros d H1 [k H2].
                     assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) by lia.
                     destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; lia.
                 --- apply Forall_nil.
      * simpl. reflexivity.
Qed.