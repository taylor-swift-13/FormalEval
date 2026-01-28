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

Example test_factorize_34 : factorize_spec 34 [2; 17].
Proof.
  unfold factorize_spec.
  split.
  - (* Goal 1: 1 <= 34 *)
    lia.
  - split.
    + (* Goal 2: Sorted Z.le [2; 17] *)
      apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * apply HdRel_cons. lia.
    + split.
      * (* Goal 3: Forall is_prime [2; 17] *)
        apply Forall_cons.
        -- (* is_prime 2 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d Hrange Hdiv. lia.
        -- apply Forall_cons.
           ++ (* is_prime 17 *)
              unfold is_prime. split.
              ** lia.
              ** intros d [Hle Hlt] Hdiv.
                 apply Z.mod_divide in Hdiv; [|lia].
                 assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16) as Hcases by lia.
                 repeat match goal with
                        | [ H : _ \/ _ |- _ ] => destruct H as [-> | H]
                        end;
                 subst; simpl in Hdiv; discriminate.
           ++ apply Forall_nil.
      * (* Goal 4: list_prod [2; 17] = 34 *)
        simpl. reflexivity.
Qed.