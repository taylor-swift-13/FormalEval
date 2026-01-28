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

Fixpoint fib_linear (n : nat) : Z * Z :=
  match n with
  | O => (0, 1)
  | S m =>
      let (fm, fm1) := fib_linear m in
      (fm1, fm + fm1)
  end.

Lemma fib_linear_correct : forall n, fib_linear n = (fib_nat n, fib_nat (S n)).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. f_equal. simpl. lia.
Qed.

Example test_fib_68 : fib_spec 68 72723460248141.
Proof.
  unfold fib_spec.
  split.
  - lia.
  - replace (fib_nat (Z.to_nat 68)) with (fst (fib_linear (Z.to_nat 68))).
    + vm_compute. reflexivity.
    + rewrite fib_linear_correct. reflexivity.
Qed.