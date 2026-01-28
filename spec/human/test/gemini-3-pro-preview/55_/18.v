Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
*)
Inductive is_fib : nat -> Z -> Prop :=
  | fib_zero : is_fib 0%nat 0
  | fib_one  : is_fib 1%nat 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  is_fib n res.

Fixpoint fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fib_iter n' b (a + b)
  end.

Definition fib_linear (n : nat) : Z := fib_iter n 0 1.

Lemma fib_iter_correct : forall n k a b,
  is_fib k a ->
  is_fib (S k) b ->
  is_fib (k + n)%nat (fib_iter n a b).
Proof.
  induction n as [|n IH]; intros k a b Ha Hb.
  - simpl. replace (k + 0)%nat with k by lia. assumption.
  - simpl.
    replace (k + S n)%nat with (S k + n)%nat by lia.
    apply IH.
    + assumption.
    + replace (a + b) with (b + a) by lia.
      apply fib_step; assumption.
Qed.

Lemma fib_linear_correct : forall n, is_fib n (fib_linear n).
Proof.
  intros n. unfold fib_linear.
  replace n with (0 + n)%nat by lia.
  apply fib_iter_correct.
  - apply fib_zero.
  - apply fib_one.
Qed.

(* Test case: input = 71, output = 308061521170129 *)
Example test_fib_71 : problem_55_spec 71%nat 308061521170129.
Proof.
  unfold problem_55_spec.
  assert (H: is_fib 71%nat (fib_linear 71%nat)).
  { apply fib_linear_correct. }
  assert (Eq: fib_linear 71%nat = 308061521170129).
  { vm_compute. reflexivity. }
  rewrite <- Eq.
  exact H.
Qed.