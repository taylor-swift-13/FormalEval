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

Example test_factorize_1000 : factorize_spec 1000 [2; 2; 2; 5; 5; 5].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + repeat (constructor; try lia).
    + split.
      * assert (H2: is_prime 2).
        { unfold is_prime. split. lia. intros d H [k Hk]. lia. }
        assert (H5: is_prime 5).
        { unfold is_prime. split. lia. intros d H [k Hk].
          assert (d = 2 \/ d = 3 \/ d = 4) by lia.
          destruct H0 as [-> | [-> | ->]].
          - assert (k <= 2 \/ k >= 3) by lia. destruct H0; lia.
          - assert (k <= 1 \/ k >= 2) by lia. destruct H0; lia.
          - assert (k <= 1 \/ k >= 2) by lia. destruct H0; lia.
        }
        repeat (constructor; try assumption).
      * simpl. reflexivity.
Qed.