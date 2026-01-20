Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8857/291"; "308435383/384"] -> x1=8857, x2=291, n1=308435383, n2=384
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 8857 291 308435383 384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that the mod is not 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.