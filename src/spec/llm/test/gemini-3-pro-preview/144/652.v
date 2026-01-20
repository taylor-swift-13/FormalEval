Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["943/29"; "943/29"] -> x1=943, x2=29, n1=943, n2=29
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 943 29 943 29 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is contradictory *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo value in the hypothesis *)
    vm_compute in H_mod.
    (* H_mod reduces to 312 = 0 (or similar non-zero value), which is contradictory *)
    discriminate H_mod.
Qed.