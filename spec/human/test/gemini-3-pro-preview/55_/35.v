Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
  Modified to use Z for the result to handle large numbers.
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

(* Test case: input = 44, output = 701408733 *)
Example test_fib_44 : problem_55_spec 44 701408733.
Proof.
  unfold problem_55_spec.
  (* We build the proof bottom-up to avoid exponential branching in the proof tree *)
  assert (H0: is_fib 0%nat 0) by apply fib_zero.
  assert (H1: is_fib 1%nat 1) by apply fib_one.
  
  assert (H2: is_fib 2%nat 1).
  { replace 1 with (1 + 0) by reflexivity.
    apply fib_step; assumption. }

  assert (H3: is_fib 3%nat 2).
  { replace 2 with (1 + 1) by reflexivity.
    apply fib_step; assumption. }

  assert (H4: is_fib 4%nat 3).
  { replace 3 with (2 + 1) by reflexivity.
    apply fib_step; assumption. }

  assert (H5: is_fib 5%nat 5).
  { replace 5 with (3 + 2) by reflexivity.
    apply fib_step; assumption. }

  assert (H6: is_fib 6%nat 8).
  { replace 8 with (5 + 3) by reflexivity.
    apply fib_step; assumption. }

  assert (H7: is_fib 7%nat 13).
  { replace 13 with (8 + 5) by reflexivity.
    apply fib_step; assumption. }

  assert (H8: is_fib 8%nat 21).
  { replace 21 with (13 + 8) by reflexivity.
    apply fib_step; assumption. }

  assert (H9: is_fib 9%nat 34).
  { replace 34 with (21 + 13) by reflexivity.
    apply fib_step; assumption. }

  assert (H10: is_fib 10%nat 55).
  { replace 55 with (34 + 21) by reflexivity.
    apply fib_step; assumption. }

  assert (H11: is_fib 11%nat 89).
  { replace 89 with (55 + 34) by reflexivity.
    apply fib_step; assumption. }

  assert (H12: is_fib 12%nat 144).
  { replace 144 with (89 + 55) by reflexivity.
    apply fib_step; assumption. }

  assert (H13: is_fib 13%nat 233).
  { replace 233 with (144 + 89) by reflexivity.
    apply fib_step; assumption. }

  assert (H14: is_fib 14%nat 377).
  { replace 377 with (233 + 144) by reflexivity.
    apply fib_step; assumption. }

  assert (H15: is_fib 15%nat 610).
  { replace 610 with (377 + 233) by reflexivity.
    apply fib_step; assumption. }

  assert (H16: is_fib 16%nat 987).
  { replace 987 with (610 + 377) by reflexivity.
    apply fib_step; assumption. }

  assert (H17: is_fib 17%nat 1597).
  { replace 1597 with (987 + 610) by reflexivity.
    apply fib_step; assumption. }

  assert (H18: is_fib 18%nat 2584).
  { replace 2584 with (1597 + 987) by reflexivity.
    apply fib_step; assumption. }

  assert (H19: is_fib 19%nat 4181).
  { replace 4181 with (2584 + 1597) by reflexivity.
    apply fib_step; assumption. }

  assert (H20: is_fib 20%nat 6765).
  { replace 6765 with (4181 + 2584) by reflexivity.
    apply fib_step; assumption. }

  assert (H21: is_fib 21%nat 10946).
  { replace 10946 with (6765 + 4181) by reflexivity.
    apply fib_step; assumption. }

  assert (H22: is_fib 22%nat 17711).
  { replace 17711 with (10946 + 6765) by reflexivity.
    apply fib_step; assumption. }

  assert (H23: is_fib 23%nat 28657).
  { replace 28657 with (17711 + 10946) by reflexivity.
    apply fib_step; assumption. }

  assert (H24: is_fib 24%nat 46368).
  { replace 46368 with (28657 + 17711) by reflexivity.
    apply fib_step; assumption. }

  assert (H25: is_fib 25%nat 75025).
  { replace 75025 with (46368 + 28657) by reflexivity.
    apply fib_step; assumption. }

  assert (H26: is_fib 26%nat 121393).
  { replace 121393 with (75025 + 46368) by reflexivity.
    apply fib_step; assumption. }

  assert (H27: is_fib 27%nat 196418).
  { replace 196418 with (121393 + 75025) by reflexivity.
    apply fib_step; assumption. }

  assert (H28: is_fib 28%nat 317811).
  { replace 317811 with (196418 + 121393) by reflexivity.
    apply fib_step; assumption. }

  assert (H29: is_fib 29%nat 514229).
  { replace 514229 with (317811 + 196418) by reflexivity.
    apply fib_step; assumption. }

  assert (H30: is_fib 30%nat 832040).
  { replace 832040 with (514229 + 317811) by reflexivity.
    apply fib_step; assumption. }

  assert (H31: is_fib 31%nat 1346269).
  { replace 1346269 with (832040 + 514229) by reflexivity.
    apply fib_step; assumption. }

  assert (H32: is_fib 32%nat 2178309).
  { replace 2178309 with (1346269 + 832040) by reflexivity.
    apply fib_step; assumption. }

  assert (H33: is_fib 33%nat 3524578).
  { replace 3524578 with (2178309 + 1346269) by reflexivity.
    apply fib_step; assumption. }

  assert (H34: is_fib 34%nat 5702887).
  { replace 5702887 with (3524578 + 2178309) by reflexivity.
    apply fib_step; assumption. }

  assert (H35: is_fib 35%nat 9227465).
  { replace 9227465 with (5702887 + 3524578) by reflexivity.
    apply fib_step; assumption. }

  assert (H36: is_fib 36%nat 14930352).
  { replace 14930352 with (9227465 + 5702887) by reflexivity.
    apply fib_step; assumption. }

  assert (H37: is_fib 37%nat 24157817).
  { replace 24157817 with (14930352 + 9227465) by reflexivity.
    apply fib_step; assumption. }

  assert (H38: is_fib 38%nat 39088169).
  { replace 39088169 with (24157817 + 14930352) by reflexivity.
    apply fib_step; assumption. }

  assert (H39: is_fib 39%nat 63245986).
  { replace 63245986 with (39088169 + 24157817) by reflexivity.
    apply fib_step; assumption. }

  assert (H40: is_fib 40%nat 102334155).
  { replace 102334155 with (63245986 + 39088169) by reflexivity.
    apply fib_step; assumption. }

  assert (H41: is_fib 41%nat 165580141).
  { replace 165580141 with (102334155 + 63245986) by reflexivity.
    apply fib_step; assumption. }

  assert (H42: is_fib 42%nat 267914296).
  { replace 267914296 with (165580141 + 102334155) by reflexivity.
    apply fib_step; assumption. }

  assert (H43: is_fib 43%nat 433494437).
  { replace 433494437 with (267914296 + 165580141) by reflexivity.
    apply fib_step; assumption. }

  (* Finally, prove for 44 *)
  replace 701408733 with (433494437 + 267914296) by reflexivity.
  apply fib_step.
  - exact H42.
  - exact H43.
Qed.