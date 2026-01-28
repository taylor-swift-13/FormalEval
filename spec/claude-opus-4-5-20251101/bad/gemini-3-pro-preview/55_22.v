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
  fib_iter n (fib_nat k) (fib_nat (S k)) = fib_nat (n + k).
Proof.
  induction n as [|n IH]; intros k.
  - simpl. rewrite Nat.add_0_l. reflexivity.
  - simpl. replace (fib_nat k + fib_nat (S k)) with (fib_nat (S (S k))).
    + rewrite IH. f_equal. lia.
    + simpl. rewrite Z.add_comm. reflexivity.
Qed.

Example test_fib_62 : fib_spec 62 4052739537881.
Proof.
  unfold fib_spec.
  split.
  - lia.
  - replace (fib_nat (Z.to_nat 62)) with (fib_iter (Z.to_nat 62) 0 1).
    + vm_compute. reflexivity.
    + change 0 with (fib_nat 0).
      change 1 with (fib_nat 1).
      rewrite fib_iter_correct.
      f_equal. lia.
Qed.