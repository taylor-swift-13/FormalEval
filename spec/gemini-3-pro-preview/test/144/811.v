Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["388/1313"; "38/113"] -> x1=388, x2=1313, n1=38, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 388 1313 38 113 false.
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
    (* Simplify algebraic expressions: (388 * 38) mod (1313 * 113) *)
    (* 388 * 38 = 14744 *)
    (* 1313 * 113 = 148369 *)
    (* 14744 mod 148369 = 14744 *)
    (* H_mod asserts 14744 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.