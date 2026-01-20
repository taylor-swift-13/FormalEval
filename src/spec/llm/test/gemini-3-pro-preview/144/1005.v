Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["99/100"; "921/739"] -> x1=99, x2=100, n1=921, n2=739
   Output: false -> result=false
*)
Example test_simplify : simplify_spec 99 100 921 739 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (99 * 921) mod (100 * 739) *)
    (* 91179 mod 73900 = 17279 *)
    (* 17279 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.