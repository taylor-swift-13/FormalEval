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

Fixpoint check_prime (d n : nat) : bool :=
  match d with
  | 0 => false
  | 1 => true
  | S d' => if (n mod d =? 0) then false else check_prime d' n
  end.

Definition is_prime_b (n : nat) : bool :=
  if n <=? 1 then false else check_prime (pred n) n.

Lemma check_prime_correct : forall d n,
  1 <= d < n ->
  check_prime d n = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k n.
Proof.
  induction d; intros Hbound Hcheck k Hk Hdiv.
  - lia.
  - simpl in Hcheck.
    destruct d.
    + lia.
    + destruct (n mod S (S d) =? 0) eqn:Hrem.
      * discriminate.
      * apply IHd in Hcheck.
        -- destruct (Nat.eq_dec k (S (S d))).
           ++ subst. apply Nat.eqb_neq in Hrem.
              apply Nat.mod_divide in Hdiv; [|lia].
              contradiction.
           ++ apply Hcheck; try lia.
        -- lia.
Qed.

Lemma is_prime_b_correct : forall n, is_prime_b n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_b in H.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    unfold is_prime. split; [assumption|].
    intros d Hdiv.
    destruct (Nat.eq_dec d 1); [left; assumption|].
    destruct (Nat.eq_dec d n); [right; assumption|].
    assert (1 < d < n).
    {
      split.
      - destruct d; [lia|]. destruct d; [congruence|lia].
      - apply Nat.divide_pos_le in Hdiv; [|lia].
        lia.
    }
    assert (Hchk: check_prime (pred n) n = true) by assumption.
    assert (Hforall: forall k, 1 < k <= pred n -> ~ Nat.divide k n).
    {
      apply check_prime_correct; try lia.
    }
    exfalso.
    apply (Hforall d); try lia.
    assumption.
Qed.

Example test_factorize_1207943 : factorize_spec 1207943 [11; 11; 67; 149].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor.
      * apply is_prime_b_correct. reflexivity.
      * apply is_prime_b_correct. reflexivity.
      * apply is_prime_b_correct. reflexivity.
      * apply is_prime_b_correct. reflexivity.
    + repeat constructor; lia.
Qed.