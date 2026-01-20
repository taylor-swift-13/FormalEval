Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/7939"; "3380/41"] -> x1=921, x2=7939, n1=3380, n2=41
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 921 7939 3380 41 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res : false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (921 * 3380) mod (7939 * 41) *)
    (* 3112980 mod 325499 = 183489 *)
    (* 183489 <> 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.