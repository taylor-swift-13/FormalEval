Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/117"; "176/117"] -> x1=176, x2=117, n1=176, n2=117
   Output: false -> result=false
*)
Example test_simplify_case : simplify_spec 176 117 176 117 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (176 * 176) mod (117 * 117) *)
    (* 176 * 176 = 30976 *)
    (* 117 * 117 = 13689 *)
    (* 30976 mod 13689 = 3598 *)
    (* 3598 <> 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.