Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["380/2"; "3280/241"] -> x1=380, x2=2, n1=3280, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 380 2 3280 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (380 * 3280) mod (2 * 241) *)
    (* 380 * 3280 = 1246400 *)
    (* 2 * 241 = 482 *)
    (* 1246400 mod 482 = 430 *)
    (* H_mod becomes 430 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.