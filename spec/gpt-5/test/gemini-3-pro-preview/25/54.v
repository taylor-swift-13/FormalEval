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

Example test_factorize_56 : factorize_spec 56 [2; 2; 2; 7].
Proof.
  unfold factorize_spec.
  split.
  - (* 1 <= 56 *)
    lia.
  - split.
    + (* Sorted Z.le [2; 2; 2; 7] *)
      repeat apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
      * apply HdRel_cons; lia.
      * apply HdRel_cons; lia.
      * apply HdRel_cons; lia.
    + split.
      * (* Forall is_prime [2; 2; 2; 7] *)
        apply Forall_cons.
        -- (* is_prime 2 *)
           unfold is_prime. split. lia. intros d H1 H2. lia.
        -- apply Forall_cons.
           ++ (* is_prime 2 *)
              unfold is_prime. split. lia. intros d H1 H2. lia.
           ++ apply Forall_cons.
              ** (* is_prime 2 *)
                 unfold is_prime. split. lia. intros d H1 H2. lia.
              ** apply Forall_cons.
                 --- (* is_prime 7 *)
                     unfold is_prime. split. lia.
                     intros d Hrange Hdiv.
                     destruct Hdiv as [k Hk].
                     assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as Hcases by lia.
                     destruct Hcases as [?|[?|[?|[?|?]]]]; subst; lia.
                 --- apply Forall_nil.
      * (* list_prod [2; 2; 2; 7] = 56 *)
        simpl. reflexivity.
Qed.