Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Fixpoint fib_nat (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S _ as m) => fib_nat m + fib_nat (pred m)
  end.

Definition fib_spec (n : Z) (result : Z) : Prop :=
  n >= 0 /\
  result = fib_nat (Z.to_nat n).

Fixpoint fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | O => a
  | S n' => fib_iter n' b (a + b)
  end.

Lemma fib_iter_correct : forall n k,
  fib_iter n (fib_nat k) (fib_nat (S k)) = fib_nat (k + n).
Proof.
  induction n as [|n IH]; intros k.
  - simpl. replace (k + 0)%nat with k by lia. reflexivity.
  - simpl.
    replace (k + S n)%nat with (S k + n)%nat by lia.
    rewrite <- IH.
    f_equal.
    simpl. rewrite Z.add_comm. reflexivity.
Qed.

Example test_fib_71 : fib_spec 71 308061521170129.
Proof.
  unfold fib_spec.
  split.
  - lia.
  - replace (Z.to_nat 71) with 71%nat by (simpl; reflexivity).
    replace (fib_nat 71) with (fib_nat (0 + 71)%nat) by (f_equal; lia).
    rewrite <- (fib_iter_correct 71 0).
    vm_compute.
    reflexivity.
Qed.