Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/291"; "9999/01"] -> x1=857, x2=291, n1=9999, n2=1
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 857 291 9999 1 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Verify that (857 * 9999) mod (291 * 1) is not 0 *)
    vm_compute in H_mod.
    (* The computation results in a non-zero value equals 0, which is a contradiction *)
    discriminate.
Qed.