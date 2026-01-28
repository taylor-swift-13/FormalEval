Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition fib4_Z (n : Z) : Z :=
  let fix fib4_aux (fuel : nat) (a b c d k : Z) : Z :=
    match fuel with
    | 0%nat => d
    | S fuel' =>
        if k <? 1 then a
        else if k <? 2 then b
        else if k <? 3 then c
        else if k <? 4 then d
        else fib4_aux fuel' b c d (a + b + c + d) (k - 1)
    end
  in fib4_aux (Z.to_nat n + 1) 0 0 2 0 n.

Definition problem_46_pre (input : Z) : Prop := True.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  output = fib4_Z input.

Example test_fib4_40 : problem_46_spec 40 36877489824.
Proof.
  unfold problem_46_spec.
  unfold fib4_Z.
  native_compute.
  reflexivity.
Qed.