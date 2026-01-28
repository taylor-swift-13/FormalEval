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
  Example Proof for the Test Case:
  Input: n = 19
  Output: res = 19513
*)
Example test_fibfib_19 : problem_63_spec 19 19513.
Proof.
  unfold problem_63_spec.
  pose (h0 := ff_zero).
  pose (h1 := ff_one).
  pose (h2 := ff_two).
  pose (h3 := ff_step 0 _ _ _ h0 h1 h2). simpl in h3.
  pose (h4 := ff_step 1 _ _ _ h1 h2 h3). simpl in h4.
  pose (h5 := ff_step 2 _ _ _ h2 h3 h4). simpl in h5.
  pose (h6 := ff_step 3 _ _ _ h3 h4 h5). simpl in h6.
  pose (h7 := ff_step 4 _ _ _ h4 h5 h6). simpl in h7.
  pose (h8 := ff_step 5 _ _ _ h5 h6 h7). simpl in h8.
  pose (h9 := ff_step 6 _ _ _ h6 h7 h8). simpl in h9.
  pose (h10 := ff_step 7 _ _ _ h7 h8 h9). simpl in h10.
  pose (h11 := ff_step 8 _ _ _ h8 h9 h10). simpl in h11.
  pose (h12 := ff_step 9 _ _ _ h9 h10 h11). simpl in h12.
  pose (h13 := ff_step 10 _ _ _ h10 h11 h12). simpl in h13.
  pose (h14 := ff_step 11 _ _ _ h11 h12 h13). simpl in h14.
  pose (h15 := ff_step 12 _ _ _ h12 h13 h14). simpl in h15.
  pose (h16 := ff_step 13 _ _ _ h13 h14 h15). simpl in h16.
  pose (h17 := ff_step 14 _ _ _ h14 h15 h16). simpl in h17.
  pose (h18 := ff_step 15 _ _ _ h15 h16 h17). simpl in h18.
  pose (h19 := ff_step 16 _ _ _ h16 h17 h18). simpl in h19.
  exact h19.
Qed.