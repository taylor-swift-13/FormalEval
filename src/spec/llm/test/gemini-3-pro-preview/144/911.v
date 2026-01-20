Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/1813"; "38/13"] -> x1=8, x2=1813, n1=38, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8 1813 38 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (8 * 38) mod (1813 * 13) evaluates to 304, which is not 0 *)
    compute in H_mod.
    discriminate H_mod.
Qed.