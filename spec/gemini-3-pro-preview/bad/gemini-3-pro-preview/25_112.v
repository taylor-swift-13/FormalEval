Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 < d -> (d | p) -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Lemma is_prime_equiv : forall p, is_prime p <-> prime p.
Proof.
  intros p. split.
  - intros [H1 H2]. split; auto.
    intros n Hn Hdiv.
    assert (0 < n) by lia.
    destruct (H2 n H Hdiv); lia.
  - intros [H1 H2]. split; auto.
    intros d Hd0 Hdiv.
    destruct (Z_le_gt_dec d 1).
    + left. lia.
    + destruct (Z_ge_lt_dec d p).
      * right. apply Z.divide_pos_le in Hdiv; lia.
      * exfalso. apply (H2 d); try split; auto.
Qed.

Ltac prove_prime :=
  apply is_prime_equiv;
  match goal with
  | |- prime ?p =>
      let x := constr:(prime_dec p) in
      let y := eval vm_compute in x in
      match y with
      | left H => exact H
      | right _ => fail "Not prime"
      end
  end.

Example test_factorize_large : factorize_spec 43121192840 [2; 2; 2; 5; 11; 98002711].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat (constructor; try prove_prime).
    + repeat (constructor; try lia).
Qed.