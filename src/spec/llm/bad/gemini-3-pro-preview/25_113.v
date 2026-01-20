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

Fixpoint check_divs (n d : nat) : bool :=
  match d with
  | 0 => true
  | 1 => true
  | _ => if (n mod d =? 0) then false else check_divs n (d - 1)
  end.

Lemma check_divs_ok : forall n d, check_divs n d = true -> forall k, 2 <= k <= d -> ~ Nat.divide k n.
Proof.
  induction d; intros H k Hk.
  - lia.
  - simpl in H. destruct d.
    + lia.
    + destruct (n mod S (S d) =? 0) eqn:E.
      * discriminate.
      * apply Nat.eqb_neq in E.
        destruct (Nat.eq_dec k (S (S d))).
        -- subst. intro C. apply Nat.mod_divide in C; try lia. contradiction.
        -- apply IHd; try assumption. lia.
Qed.

Lemma is_prime_check : forall p, 
  1 < p -> 
  check_divs p (p - 1) = true -> 
  is_prime p.
Proof.
  intros p H1 Hc.
  split; auto.
  intros d Hd.
  destruct (Nat.eq_dec d 1); auto.
  destruct (Nat.eq_dec d p); auto.
  exfalso.
  assert (2 <= d <= p - 1).
  { split. 
    - destruct d; try lia. destruct d; try lia.
    - apply Nat.divide_pos_le in Hd; try lia. }
  eapply check_divs_ok; eauto.
Qed.

Example test_factorize_1207946 : factorize_spec 1207946 [2; 31; 19483].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + constructor.
      * apply is_prime_check; try lia. reflexivity.
      * constructor.
        -- apply is_prime_check; try lia. reflexivity.
        -- constructor.
           ++ apply is_prime_check; try lia. vm_compute. reflexivity.
           ++ constructor.
    + repeat constructor.
Qed.