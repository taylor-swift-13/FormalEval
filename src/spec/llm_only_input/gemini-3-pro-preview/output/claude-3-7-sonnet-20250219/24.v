Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition largest_divisor_spec (n d : Z) : Prop :=
  1 < n ->
  1 < d < n /\
  n mod d = 0 /\
  (forall k, 1 < k < n -> n mod k = 0 -> d <= k).

(* 
   Test case: input = 3, output = 1.
   We prove the negation of the specification because for n = 3 and d = 1,
   the condition 1 < d < n (i.e., 1 < 1 < 3) is false.
   The specification requires the divisor to be strictly greater than 1.
*)
Example test_case_3_1 : ~ largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  intros H.
  (* Establish the premise 1 < 3 *)
  assert (H_prem : 1 < 3) by lia.
  (* Apply the hypothesis *)
  apply H in H_prem.
  (* Decompose the result. The first part is 1 < 1 < 3 *)
  destruct H_prem as [H_range _].
  (* This leads to a contradiction as 1 < 1 is false *)
  lia.
Qed.