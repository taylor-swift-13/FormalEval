Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9943/29"; "138/113"] -> x1=9943, x2=29, n1=138, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9943 29 138 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Check the modulo calculation: (9943 * 138) mod (29 * 113) *)
    (* 1372134 mod 3277 = 2348 *)
    (* 2348 <> 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.