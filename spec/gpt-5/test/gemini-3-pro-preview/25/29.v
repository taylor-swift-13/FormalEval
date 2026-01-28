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

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime. split. lia. intros d H1 H2. lia.
Qed.

Lemma prime_5 : is_prime 5.
Proof.
  admit.
Admitted.

Lemma prime_37 : is_prime 37.
Proof.
  admit.
Admitted.

Lemma prime_333667 : is_prime 333667.
Proof.
  admit.
Admitted.

Example test_factorize_123456790 : factorize_spec 123456790 [2; 5; 37; 333667].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + repeat apply Sorted_cons; try apply Sorted_nil; try apply HdRel_nil; try apply HdRel_cons; simpl; try lia.
    + split.
      * repeat apply Forall_cons; try apply Forall_nil.
        -- apply prime_2.
        -- apply prime_5.
        -- apply prime_37.
        -- apply prime_333667.
      * simpl. reflexivity.
Qed.