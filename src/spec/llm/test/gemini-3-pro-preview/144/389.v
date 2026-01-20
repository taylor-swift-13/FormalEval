Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4637/77636"; "9943/29"] -> x1=4637, x2=77636, n1=9943, n2=29
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 4637 77636 9943 29 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo arithmetic *)
    vm_compute in H_mod.
    (* The computed remainder is not 0, so we have a contradiction *)
    discriminate.
Qed.