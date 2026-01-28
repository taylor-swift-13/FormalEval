Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Definition divides_b (d n : nat) : bool :=
  (n mod d =? 0).

Definition check_prime_range (p : nat) : bool :=
  match p with
  | 0 => false
  | 1 => false
  | _ => forallb (fun d => negb (divides_b d p)) (seq 2 (p - 2))
  end.

Lemma check_prime_correct : forall p, check_prime_range p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime_range in H.
  destruct p as [| [| p'] ]; try discriminate.
  assert (p_gt_1 : S (S p') > 1) by lia.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1) as [Hle1 | Hgt1].
  - destruct d; try lia. left. reflexivity.
  - destruct (le_lt_dec (S (S p')) d) as [HleP | HltP].
    + apply Nat.divide_pos_le in Hdiv; try lia.
      right. lia.
    + assert (Hin: In d (seq 2 (S (S p') - 2))).
      { apply in_seq. split; lia. }
      rewrite forallb_forall in H.
      specialize (H d Hin).
      unfold divides_b in H.
      apply negb_true_iff in H.
      apply Nat.eqb_neq in H.
      apply Nat.mod_divide in Hdiv; try lia.
      congruence.
Qed.

Example test_factorize_1207942 : factorize_spec 1207942 [2; 41; 14731].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + constructor.
      * apply check_prime_correct. vm_compute. reflexivity.
      * constructor.
        -- apply check_prime_correct. vm_compute. reflexivity.
        -- constructor.
           ++ apply check_prime_correct. vm_compute. reflexivity.
           ++ constructor.
    + repeat (constructor; try lia).
Qed.