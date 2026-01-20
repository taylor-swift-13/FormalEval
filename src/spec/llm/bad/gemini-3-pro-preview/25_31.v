Existing Coq output file content specification for the first test case `input = [2%Z], output = [2%Z]`:
```coq
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma prime_sqrt_check : forall p,
  1 < p ->
  (forall d, 2 <= d -> d * d <= p -> p mod d <> 0) ->
  is_prime p.
Proof.
  intros p Hp Hchk.
  split; [assumption|].
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); [left; assumption|].
  destruct (Nat.eq_dec d p); [right; assumption|].
  exfalso.
  assert (d <> 0). { intro. subst. destruct Hdiv. simpl in H. lia. }
  apply Nat.mod_divide in Hdiv; [|assumption].
  destruct (le_lt_dec (d * d) p).
  - apply (Hchk d) in l; [contradiction| |assumption].
    destruct d; [lia|]. destruct d; [lia|]. lia.
  - assert (exists q, p = q * d).
    { exists (p / d). rewrite Nat.mul_comm. apply Nat.div_exact; assumption. }
    destruct H as [q Hq].
    assert (q <> 1). { intro. subst. rewrite Nat.mul_1_l in Hq. lia. }
    assert (q <> 0). { intro. subst. simpl in Hq. lia. }
    assert (2 <= q) by lia.
    assert (q * q <= p).
    {
       destruct (le_lt_dec d q).
       - assert (d * d <= q * d) by (apply Nat.mul_le_mono_r; assumption).
         rewrite <- Hq in H1. lia.
       - assert (q * q < q * d) by (apply Nat.mul_lt_mono_pos_l; lia).
         rewrite <- Hq in H1. lia.
    }
    apply (Hchk q) in H1; [|assumption].
    rewrite Hq in H1.
    rewrite Nat.mod_mul in H1; [contradiction|assumption].
Qed.

Example test_factorize_123456788 : factorize_spec 123456788 [2; 2; 7; 13; 17; 71; 281].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    simpl. reflexivity.
  - split.
    + (* Primality check *)
      repeat constructor.
      all: try (apply prime_sqrt_check; [lia|]; intros d Hle Hsq).
      all: try (
        (* Iterate d from 2 up to sqrt(p) *)
        do 18 (destruct d as [|d]; [ lia | 
          match goal with
          | [ |- _ mod _ <> 0 ] => vm_compute; discriminate
          | _ => idtac
          end
        ]);
        (* If d is still large, d*d > p contradicts Hsq *)
        simpl in Hsq; lia
      ).
    + (* Sorted check *)
      repeat constructor; lia.
Qed.