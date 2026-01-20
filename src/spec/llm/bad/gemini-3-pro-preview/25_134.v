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

(* Helper definitions and lemmas for primality checking *)

Fixpoint check_prime (d p : nat) : bool :=
  match d with
  | 0 => false
  | 1 => true
  | S d' => if (p mod (S d') =? 0) then false else check_prime d' p
  end.

Definition is_prime_b (p : nat) : bool :=
  if p <=? 1 then false else check_prime (pred p) p.

Lemma check_prime_correct : forall d p,
  check_prime d p = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k p.
Proof.
  induction d; intros p Hcheck k Hk Hdiv.
  - discriminate.
  - destruct d.
    + lia.
    + simpl in Hcheck.
      destruct (p mod S (S d) =? 0) eqn:Hrem.
      * discriminate.
      * apply Nat.eqb_neq in Hrem.
        assert (k = S (S d) \/ k <= S d) as [Heq|Hle] by lia.
        -- subst. apply Hrem. apply Nat.mod_divide; [lia|assumption].
        -- apply IHd with (k:=k) in Hcheck; [apply Hcheck; assumption|lia].
Qed.

Lemma is_prime_b_correct : forall p, is_prime_b p = true -> is_prime p.
Proof.
  intros p H.
  unfold is_prime_b in H.
  destruct (p <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_nle in Hle.
    split; [lia|].
    intros d Hdiv.
    destruct (le_lt_dec p d).
    + apply Nat.divide_pos_le in Hdiv; [|lia].
      right. lia.
    + destruct (le_lt_dec d 1).
      * destruct d; [destruct Hdiv as [x Hx]; rewrite Nat.mul_0_r in Hx; discriminate|].
        assert (d=1) by lia. left. assumption.
      * exfalso.
        assert (d <= pred p) by lia.
        apply check_prime_correct with (d := pred p) (k := d) in H; auto.
Qed.

Example test_factorize_1207948 : factorize_spec 1207948 [2; 2; 7; 7; 6163].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor; apply is_prime_b_correct; vm_compute; reflexivity.
    + repeat (apply Sorted_cons; [| constructor; lia]). apply Sorted_nil.
Qed.