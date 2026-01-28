Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
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

Fixpoint check_range (d : Z) (count : nat) (p : Z) : bool :=
  match count with
  | O => true
  | S c => if (p mod d =? 0) then false else check_range (d + 1) c p
  end.

Lemma check_range_sound : forall count d p,
  d > 0 ->
  check_range d count p = true ->
  (forall k, d <= k < d + Z.of_nat count -> ~(k | p)).
Proof.
  induction count; intros d p Hpos Hres k Hk.
  - lia.
  - simpl in Hres.
    destruct (p mod d =? 0) eqn:Heq.
    + discriminate.
    + apply Z.eqb_neq in Heq.
      destruct (Z.eq_dec k d).
      * subst k. intro Hdiv.
        apply Z.mod_divide in Hdiv; auto.
        lia.
      * apply IHcount with (d+1); auto.
        -- lia.
        -- lia.
Qed.

Definition check_prime_bool (p : Z) : bool :=
  if p <=? 1 then false
  else check_range 2 (Z.to_nat (p - 2)) p.

Lemma check_prime_bool_sound : forall p,
  check_prime_bool p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime_bool in H.
  destruct (p <=? 1) eqn:Hle.
  - discriminate.
  - apply Z.leb_nle in Hle.
    unfold is_prime. split; [lia|].
    intros d Hpos Hdiv.
    apply check_range_sound with (k:=d) in H; try lia.
    + destruct (Z_eq_dec d 1); [left; auto|].
      destruct (Z_eq_dec d p); [right; auto|].
      exfalso.
      apply H.
      * split.
        -- lia.
        -- rewrite Z2Nat.id; lia.
      * assumption.
    + lia.
Qed.

Example test_factorize_43121192842 : factorize_spec 43121192842 [2; 7; 13; 5717; 41443].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor.
      all: apply check_prime_bool_sound.
      all: vm_compute; reflexivity.
    + repeat constructor.
      all: vm_compute; try lia.
Qed.