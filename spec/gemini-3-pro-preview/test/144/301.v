Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4688/1386"; "30802/24"] -> x1=4688, x2=1386, n1=30802, n2=24
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4688 1386 30802 24 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo value to show it is not 0 *)
    (* (4688 * 30802) mod (1386 * 24) reduces to 4352 *)
    vm_compute in H_mod.
    (* 4352 = 0 is a contradiction *)
    discriminate H_mod.
Qed.