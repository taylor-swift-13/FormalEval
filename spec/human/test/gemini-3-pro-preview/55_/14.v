Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
  We use Z to accommodate large Fibonacci numbers that exceed nat's practical limits.
*)
Inductive is_fib : Z -> Z -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (n + 1) res_n1 ->
               is_fib (n + 2) (res_n1 + res_n).

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  is_fib n res.

(* Test case: input = 63, output = 6557470319842 *)
Example test_fib_63 : problem_55_spec 63 6557470319842.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.

  (* Tactic to compute the next Fibonacci number from the last two in the context *)
  Ltac step_fib :=
    match goal with
    | [ Ha : is_fib ?na ?ra, Hb : is_fib ?nb ?rb |- _ ] =>
      let diff := eval compute in (nb - na) in
      match diff with
      | 1 =>
        let next_n := eval compute in (nb + 1) in
        let next_r := eval compute in (ra + rb) in
        assert (is_fib next_n next_r) by (apply (fib_step na ra rb); assumption);
        clear Ha (* Clear the oldest to keep context clean *)
      end
    end.

  (* We start with 0 and 1. We need to reach 63.
     Each step adds one index.
     We need 62 steps to go from index 1 to 63. *)
  do 62 step_fib.

  (* The goal is now in the context *)
  match goal with
  | [ H : is_fib 63 _ |- _ ] => exact H
  end.
Qed.