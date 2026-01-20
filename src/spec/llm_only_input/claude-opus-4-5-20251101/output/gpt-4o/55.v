Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

(* Define a proper Fibonacci function *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

(* The specification from the problem *)
Definition fib_spec (n : nat) (fib_n : nat) : Prop :=
  (n = 0 -> fib_n = 0) /\
  (n = 1 \/ n = 2 -> fib_n = 1) /\
  (n >= 3 -> exists a b, 
    a = 1 /\ b = 1 /\ 
    (forall i, 3 <= i <= n -> exists a_i b_i, 
      a_i = b /\ b_i = a + b /\ a = a_i /\ b = b_i) /\ 
    fib_n = b).

(* Test case using Z *)
Open Scope Z_scope.

Definition fib_Z (n : Z) : Z :=
  Z.of_nat (fib (Z.to_nat n)).

Example fib_test_10_55 : fib_Z 10 = 55.
Proof.
  unfold fib_Z.
  simpl.
  reflexivity.
Qed.

Close Scope Z_scope.

(* Also prove using nat directly *)
Example fib_nat_10_55 : fib 10 = 55.
Proof.
  simpl.
  reflexivity.
Qed.

(* Prove fib_spec for n=10 and fib_n=55 would require the spec to be satisfiable,
   but the given spec has issues (a and b are quantified but then expected to change).
   Instead, let's show the computation is correct. *)

(* A cleaner specification *)
Definition fib_spec_simple (n : nat) (fib_n : nat) : Prop :=
  fib_n = fib n.

Example fib_spec_simple_10_55 : fib_spec_simple 10 55.
Proof.
  unfold fib_spec_simple.
  simpl.
  reflexivity.
Qed.