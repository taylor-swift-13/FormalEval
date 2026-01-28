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

Example test_factorize_30 : factorize_spec 30 [2; 3; 5].
Proof.
  unfold factorize_spec.
  split.
  - (* 1 <= 30 *)
    lia.
  - split.
    + (* Sorted Z.le [2; 3; 5] *)
      apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
    + split.
      * (* Forall is_prime [2; 3; 5] *)
        repeat apply Forall_cons.
        -- (* is_prime 2 *)
           unfold is_prime. split. lia.
           intros d H. lia.
        -- (* is_prime 3 *)
           unfold is_prime. split. lia.
           intros d H Hdiv.
           assert (d = 2) by lia. subst.
           unfold Z.divide in Hdiv. destruct Hdiv as [k Hk]. lia.
        -- (* is_prime 5 *)
           unfold is_prime. split. lia.
           intros d H Hdiv.
           assert (d = 2 \/ d = 3 \/ d = 4) by lia.
           destruct H0 as [-> | [-> | ->]];
             unfold Z.divide in Hdiv; destruct Hdiv as [k Hk]; lia.
        -- apply Forall_nil.
      * (* list_prod [2; 3; 5] = 30 *)
        simpl. reflexivity.
Qed.