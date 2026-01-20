Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9943/29"; "453/38"] -> x1=9943, x2=29, n1=453, n2=38
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9943 29 453 38 false.
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
    (* Calculate (9943 * 453) mod (29 * 38) *)
    (* (9943 * 453) = 4504179 *)
    (* (29 * 38) = 1102 *)
    (* 4504179 mod 1102 = 305 *)
    (* 305 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.