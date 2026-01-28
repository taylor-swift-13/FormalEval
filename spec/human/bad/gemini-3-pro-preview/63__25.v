Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

(*
  is_fibfib n res is an inductively defined proposition asserting "res is the n-th FibFib number".
  This definition is translated directly from the mathematical definition of the fibfib function.
*)
Inductive is_fibfib : nat -> nat -> Prop :=
  (* Base Case 1: The 0th FibFib number is 0 *)
  | ff_zero : is_fibfib 0 0

  (* Base Case 2: The 1st FibFib number is 0 *)
  | ff_one  : is_fibfib 1 0

  (* Base Case 3: The 2nd FibFib number is 1 *)
  | ff_two  : is_fibfib 2 1

  (*
    Inductive Step:
    If res_n, res_n1, res_n2 are the n-th, (n+1)-th, and (n+2)-th FibFib numbers respectively,
    then the (n+3)-th FibFib number is the sum of these three.
  *)
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.

(*
  problem_63_spec is the program specification for the fibfib function.
  It states that for any input n, the result res must satisfy the is_fibfib predicate.
*)
Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

(* 
  Tail-recursive helper to compute fibfib efficiently.
  k is the number of steps remaining.
  a, b, c are the current three consecutive fibfib numbers.
*)
Fixpoint fibfib_iter (k : nat) (a b c : nat) : nat :=
  match k with
  | 0 => a
  | S k' => fibfib_iter k' b c (a + b + c)
  end.

(*
  Computable function for fibfib.
*)
Definition fibfib_compute (n : nat) : nat :=
  fibfib_iter n 0 0 1.

(*
  Lemma proving that fibfib_iter preserves the is_fibfib property.
*)
Lemma fibfib_iter_sound : forall k n a b c,
  is_fibfib n a ->
  is_fibfib (S n) b ->
  is_fibfib (S (S n)) c ->
  is_fibfib (n + k) (fibfib_iter k a b c).
Proof.
  induction k; intros; simpl.
  - rewrite Nat.add_0_r. assumption.
  - rewrite Nat.add_succ_r. apply IHk.
    + assumption.
    + assumption.
    + apply ff_step; assumption.
Qed.

(*
  Soundness theorem for the computable function.
*)
Lemma fibfib_compute_sound : forall n, is_fibfib n (fibfib_compute n).
Proof.
  intros. unfold fibfib_compute.
  replace n with (0 + n) by reflexivity.
  apply fibfib_iter_sound.
  - apply ff_zero.
  - apply ff_one.
  - apply ff_two.
Qed.

(* 
  Example Proof for the Test Case:
  Input: n = 26
  Output: res = 1389537
*)
Example test_fibfib_26 : problem_63_spec 26 1389537.
Proof.
  unfold problem_63_spec.
  replace 1389537 with (fibfib_compute 26).
  - apply fibfib_compute_sound.
  - vm_compute. reflexivity.
Qed.