Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3280/241"; "380/2"] -> x1=3280, x2=241, n1=380, n2=2
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 3280 241 380 2 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3280 * 380) mod (241 * 2) *)
    (* 3280 * 380 = 1246400 *)
    (* 241 * 2 = 482 *)
    (* 1246400 mod 482 = 430 *)
    (* 430 = 0 is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.