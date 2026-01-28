Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["380/241"; "380/241"] -> x1=380, x2=241, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 380 241 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the arithmetic: (380 * 380) mod (241 * 241) *)
    (* 144400 mod 58081 = 28238 *)
    vm_compute in H_mod.
    (* 28238 = 0 is impossible *)
    discriminate H_mod.
Qed.