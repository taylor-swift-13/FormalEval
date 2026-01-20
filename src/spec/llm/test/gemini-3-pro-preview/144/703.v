Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/77225"; "7/725"] -> x1=7, x2=77225, n1=7, n2=725
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 77225 7 725 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (7 * 7) mod (77225 * 725) evaluates to 49, which is not 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.