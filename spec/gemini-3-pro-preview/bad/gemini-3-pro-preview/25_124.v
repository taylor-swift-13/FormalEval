Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 < d -> (d | p) -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Lemma Z_prime_is_prime : forall p, prime p -> is_prime p.
Proof.
  intros p Hp.
  destruct Hp as [Hp1 Hp2].
  split; try assumption.
  intros d Hd0 Hdiv.
  assert (Hle: d <= p).
  { apply Z.divide_pos_le; try assumption. lia. }
  assert (Hnot: 1 < d < p -> False).
  { intros Hrange. apply (Hp2 d Hrange). assumption. }
  destruct (Z.eq_dec d 1); [left; assumption|].
  destruct (Z.eq_dec d p); [right; assumption|].
  exfalso. apply Hnot. split; lia.
Qed.

Example test_factorize_987654319 : factorize_spec 987654319 [987654319].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * apply Z_prime_is_prime.
        assert (H: prime 987654319).
        {
          pose (d := prime_dec 987654319).
          vm_compute in d.
          destruct d; [assumption|discriminate].
        }
        exact H.
      * constructor.
    + repeat constructor.
Qed.