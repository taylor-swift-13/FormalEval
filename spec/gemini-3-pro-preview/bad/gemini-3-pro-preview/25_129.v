Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 <= d -> (d | p) -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Lemma prime_of_Znumtheory_implies_is_prime : forall p, prime p -> is_prime p.
Proof.
  intros p Hp.
  destruct Hp as [Hgt Hdiv].
  split; auto.
  intros d Hge Hd.
  destruct (Z.eq_dec d 1); subst; auto.
  destruct (Z.eq_dec d p); subst; auto.
  assert (d <= p).
  { apply Z.divide_pos_le; auto with zarith. }
  assert (d <> 0).
  { intro; subst. apply Hdiv with 2. lia. exists 0; auto. }
  assert (1 < d < p) by lia.
  specialize (Hdiv d H1).
  contradiction.
Qed.

Ltac solve_prime :=
  match goal with
  | [ |- prime ?p ] =>
    let x := constr:(prime_dec p) in
    let y := eval vm_compute in x in
    match y with
    | left ?H => exact H
    | right _ => fail "Not a prime"
    end
  end.

Example test_factorize_large : factorize_spec 43121192837 [769; 2383; 23531].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor; apply prime_of_Znumtheory_implies_is_prime; solve_prime.
    + repeat constructor.
Qed.