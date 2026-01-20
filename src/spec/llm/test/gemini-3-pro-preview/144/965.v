Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/77"; "03080/241"] -> x1=11, x2=77, n1=3080, n2=241
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 11 77 3080 241 false.
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
    (* Compute the modulo value to show it is not 0 *)
    vm_compute in H_mod.
    (* 15323 = 0 is a contradiction *)
    discriminate H_mod.
Qed.