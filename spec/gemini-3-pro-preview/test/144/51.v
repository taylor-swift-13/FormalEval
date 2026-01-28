Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["13/199"; "13/19"] -> x1=13, x2=199, n1=13, n2=19
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 13 199 13 19 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (13 * 13) mod (199 * 19) *)
    (* 169 mod 3781 = 169 *)
    (* Hypothesis becomes 169 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.