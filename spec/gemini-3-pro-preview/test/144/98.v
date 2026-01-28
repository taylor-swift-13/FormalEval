Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["15/1117"; "15/117"] -> x1=15, x2=1117, n1=15, n2=117
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 15 1117 15 117 false.
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
    (* Simplify algebraic expressions: (15 * 15) mod (1117 * 117) *)
    (* 15 * 15 = 225 *)
    (* 1117 * 117 = 130689 *)
    (* 225 mod 130689 = 225 *)
    (* 225 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.