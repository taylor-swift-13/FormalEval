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

Example test_factorize_2 : factorize_spec 2 [2].
Proof.
  unfold factorize_spec.
  (* Manually split the conjunctions to ensure correct goal counting *)
  split.
  - (* Goal 1: 1 <= 2 *)
    lia.
  - split.
    + (* Goal 2: Sorted Z.le [2] *)
      apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + split.
      * (* Goal 3: Forall is_prime [2] *)
        apply Forall_cons.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hrange Hdiv. lia.
        -- apply Forall_nil.
      * (* Goal 4: list_prod [2] = 2 *)
        simpl. reflexivity.
Qed.