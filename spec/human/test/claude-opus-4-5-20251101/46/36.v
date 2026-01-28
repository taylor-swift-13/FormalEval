Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition fib4_Z (n : Z) : Z :=
  let fix fib4_aux (fuel : nat) (a b c d : Z) (k : Z) : Z :=
    match fuel with
    | O => d
    | S fuel' =>
      if Z.ltb k 1 then a
      else if Z.ltb k 2 then b
      else if Z.ltb k 3 then c
      else if Z.ltb k 4 then d
      else fib4_aux fuel' b c d (a + b + c + d) (k - 1)
    end
  in fib4_aux (Z.to_nat n) 0 0 2 0 n.

Fixpoint fib4_iter (n : nat) (a b c d : Z) : Z :=
  match n with
  | O => a
  | S O => b
  | S (S O) => c
  | S (S (S O)) => d
  | S n' => fib4_iter n' b c d (a + b + c + d)
  end.

Definition fib4_nat (n : nat) : Z :=
  fib4_iter n 0 0 2 0.

Definition problem_46_pre (input : Z) : Prop := (input >= 0)%Z.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  output = fib4_nat (Z.to_nat input).

Example test_fib4_83 : problem_46_spec 83 66392714182364268855232.
Proof.
  unfold problem_46_spec.
  native_compute.
  reflexivity.
Qed.