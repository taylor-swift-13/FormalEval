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

Fixpoint check_divs (d n : nat) : bool :=
  match d with
  | 0 | 1 => true
  | S d' => if (n mod (S d') =? 0) then false else check_divs d' n
  end.

Lemma check_divs_true : forall d n, check_divs d n = true -> forall k, 1 < k <= d -> ~ (Nat.divide k n).
Proof.
  induction d; intros.
  - lia.
  - destruct d.
    + simpl in H. lia.
    + simpl in H. destruct (n mod (S (S d)) =? 0) eqn:E.
      * discriminate.
      * apply IHd in H.
        intros k0 Hk0.
        destruct (Nat.eq_dec k0 (S (S d))).
        -- subst. intro Hdiv. apply Nat.mod_divide in Hdiv; auto.
           rewrite Hdiv in E. discriminate.
           lia.
        -- apply H. lia.
Qed.

Lemma is_prime_check : forall p, 1 < p -> check_divs (pred p) p = true -> is_prime p.
Proof.
  intros p Hp Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_gt_dec d 1).
  - destruct d; [lia | left; lia].
  - destruct (le_gt_dec d (pred p)).
    + assert (d <= pred p) by lia.
      apply check_divs_true with (k:=d) in Hcheck; auto.
      contradiction.
    + apply Nat.divide_pos_le in Hdiv; [|lia].
      right. lia.
Qed.

Example test_factorize_9999999964 : 
  factorize_spec (2 * 2 * 17 * 17 * 31 * 173 * 1613) [2; 2; 17; 17; 31; 173; 1613].
Proof.
  unfold factorize_spec.
  split.
  - simpl. lia.
  - split.
    + repeat (constructor; [apply is_prime_check; [lia | vm_compute; reflexivity] | ]).
      apply Forall_nil.
    + repeat constructor; lia.
Qed.