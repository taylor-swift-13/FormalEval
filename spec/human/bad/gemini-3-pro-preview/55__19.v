Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
  We use Z (integers) to handle large numbers efficiently.
*)
Inductive is_fib : Z -> Z -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (n + 1) res_n1 ->
               is_fib (n + 2) (res_n1 + res_n).

Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  is_fib n res.

(* Helper function to compute Fibonacci efficiently using tail recursion *)
Fixpoint fib_aux (k : nat) (a b : Z) : Z :=
  match k with
  | O => a
  | S k' => fib_aux k' b (a + b)
  end.

(* 
   Lemma proving that fib_aux computes the correct Fibonacci number relative to a starting point.
   We prove: if 'a' is Fib(m) and 'b' is Fib(m+1), then 'fib_aux k a b' is Fib(m+k).
*)
Lemma fib_aux_correct : forall k m a b,
  is_fib m a ->
  is_fib (m + 1) b ->
  is_fib (m + Z.of_nat k) (fib_aux k a b).
Proof.
  induction k as [| k' IH]; intros m a b Ha Hb.
  - simpl. replace (m + Z.of_nat 0) with m by lia. assumption.
  - simpl.
    (* Key step: Rewrite the index arithmetic to match the Induction Hypothesis *)
    replace (m + Z.of_nat (S k')) with ((m + 1) + Z.of_nat k') by lia.
    apply IH.
    + assumption.
    + replace (m + 1 + 1) with (m + 2) by lia.
      eapply fib_step; assumption.
Qed.

(* Test case: input = 72, output = 498454011879264 *)
Example test_fib_72 : problem_55_spec 72 498454011879264.
Proof.
  unfold problem_55_spec.
  (* 
     We use the helper lemma to jump directly to 72.
     We start at m=0 (fib 0, fib 1) and take k=72 steps.
  *)
  replace 72 with (0 + Z.of_nat 72) by lia.
  replace 498454011879264 with (fib_aux 72 0 1) by reflexivity.
  apply fib_aux_correct.
  - apply fib_zero.
  - apply fib_one.
Qed.