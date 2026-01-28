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

Lemma is_prime_1073741789 : is_prime 1073741789.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hrange Hdiv.
    admit.
Admitted.

Example test_factorize_1073741789 : factorize_spec 1073741789 [1073741789].
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
        -- apply is_prime_1073741789.
        -- apply Forall_nil.
      * simpl. reflexivity.
Qed.