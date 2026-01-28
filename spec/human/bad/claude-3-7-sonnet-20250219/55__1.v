Require Import Coq.Init.Nat.

Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

Example fib_10_test : problem_55_spec 10 55.
Proof.
  unfold problem_55_spec.
  (* Base cases *)
  pose proof fib_zero as H0.
  pose proof fib_one as H1.

  (* Construct fib 2 = 1 *)
  assert (H2: is_fib 2 1).
  { apply fib_step with (res_n:=0) (res_n1:=1); assumption. }

  (* fib 3 = 2 *)
  assert (H3: is_fib 3 2).
  { apply fib_step with (res_n:=1) (res_n1:=1); [apply H2 | apply H1]. }

  (* fib 4 = 3 *)
  assert (H4: is_fib 4 3).
  { apply fib_step with (res_n:=2) (res_n1:=1); [apply H3 | apply H2]. }

  (* fib 5 = 5 *)
  assert (H5: is_fib 5 5).
  { apply fib_step with (res_n:=3) (res_n1:=2); [apply H4 | apply H3]. }

  (* fib 6 = 8 *)
  assert (H6: is_fib 6 8).
  { apply fib_step with (res_n:=5) (res_n1:=3); [apply H5 | apply H4]. }

  (* fib 7 = 13 *)
  assert (H7: is_fib 7 13).
  { apply fib_step with (res_n:=8) (res_n1:=5); [apply H6 | apply H5]. }

  (* fib 8 = 21 *)
  assert (H8: is_fib 8 21).
  { apply fib_step with (res_n:=13) (res_n1:=8); [apply H7 | apply H6]. }

  (* fib 9 = 34 *)
  assert (H9: is_fib 9 34).
  { apply fib_step with (res_n:=21) (res_n1:=13); [apply H8 | apply H7]. }

  (* fib 10 = 55 *)
  apply fib_step with (res_n:=34) (res_n1:=21); assumption.
Qed.