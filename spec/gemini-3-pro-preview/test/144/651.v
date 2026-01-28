Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["380/241"; "8/113"] -> x1=380, x2=241, n1=8, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 380 241 8 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (380 * 8) mod (241 * 113) *)
    (* 380 * 8 = 3040 *)
    (* 241 * 113 = 27233 *)
    (* 3040 mod 27233 = 3040 *)
    vm_compute in H_mod.
    (* H_mod is now 3040 = 0, which is false *)
    discriminate H_mod.
Qed.