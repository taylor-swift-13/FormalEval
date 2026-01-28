Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Fixpoint fib_tail_aux (n : nat) (a b : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fib_tail_aux n' b (a + b)
  end.

Definition fib_tail (n : nat) : nat := fib_tail_aux n 0 1.

Lemma fib_tail_aux_correct : forall n a b k,
  fib_tail_aux n (fib k * a + fib (S k) * b) (fib (S k) * a + fib (S (S k)) * b) =
  fib (n + k) * a + fib (n + S k) * b.
Proof.
  induction n; intros.
  - simpl. reflexivity.
  - simpl fib_tail_aux.
    replace (fib (S k) * a + fib (S (S k)) * b + (fib k * a + fib (S k) * b))
      with (fib (S k) * a + fib k * a + (fib (S (S k)) * b + fib (S k) * b)) by lia.
    replace (fib (S k) * a + fib k * a) with ((fib k + fib (S k)) * a) by lia.
    replace (fib (S (S k)) * b + fib (S k) * b) with ((fib (S k) + fib (S (S k))) * b) by lia.
    simpl fib.
    rewrite IHn.
    replace (n + S k) with (S (n + k)) by lia.
    replace (n + S (S k)) with (S (S (n + k))) by lia.
    reflexivity.
Qed.

Lemma fib_tail_correct : forall n, fib_tail n = fib n.
Proof.
  intros.
  unfold fib_tail.
  replace 0 with (fib 0 * 1 + fib 1 * 0) by (simpl; lia).
  replace 1 with (fib 1 * 1 + fib 2 * 0) by (simpl; lia).
  rewrite fib_tail_aux_correct.
  simpl. lia.
Qed.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example test_fib_72 : problem_55_spec 72 498454011879264.
Proof.
  unfold problem_55_spec.
  rewrite <- fib_tail_correct.
  native_compute.
  reflexivity.
Qed.