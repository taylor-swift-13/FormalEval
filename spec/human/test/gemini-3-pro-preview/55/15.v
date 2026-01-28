Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(*
  fib is a recursive function defining the Fibonacci sequence.
  We use Z for the return type to handle large values.
*)
Fixpoint fib (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S n' => match n' with
    | 0%nat => 1
    | S n'' => fib n'' + fib n'
    end
  end.

(*
  fib_spec is the specification for the fib function.
*)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  res = fib n.

(* 
   Auxiliary linear-time function to compute Fibonacci numbers efficiently.
   This is necessary because the naive exponential definition of fib
   causes a timeout for n = 64.
*)
Fixpoint fib_linear (n : nat) : Z * Z :=
  match n with
  | 0%nat => (0, 1)
  | S n' => let (a, b) := fib_linear n' in (b, a + b)
  end.

(* Proof that the linear function is equivalent to the definition *)
Lemma fib_linear_correct_aux : forall n, fib_linear n = (fib n, fib (S n)).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma fib_linear_correct : forall n, fst (fib_linear n) = fib n.
Proof.
  intros. rewrite fib_linear_correct_aux. reflexivity.
Qed.

(* Test case: input = 64, output = 10610209857723 *)
Example problem_55_test : problem_55_spec 64%nat 10610209857723.
Proof.
  unfold problem_55_spec.
  rewrite <- fib_linear_correct.
  vm_compute.
  reflexivity.
Qed.