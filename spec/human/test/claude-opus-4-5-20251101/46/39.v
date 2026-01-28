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
      if Z.eqb k n then d
      else fib4_aux fuel' b c d (a + b + c + d) (k + 1)
    end
  in
  if Z.ltb n 0 then 0
  else if Z.eqb n 0 then 0
  else if Z.eqb n 1 then 0
  else if Z.eqb n 2 then 2
  else if Z.eqb n 3 then 0
  else fib4_aux (Z.to_nat n) 0 0 2 0 3.

Definition problem_46_pre (input : Z) : Prop := (input >= 0)%Z.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  output = fib4_Z input.

Example test_fib4_100 : problem_46_spec 100 4647959998589498844128566416.
Proof.
  unfold problem_46_spec.
  unfold fib4_Z.
  native_compute.
  reflexivity.
Qed.