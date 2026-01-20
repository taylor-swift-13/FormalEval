Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/338436"; "468/136"] -> x1=453, x2=338436, n1=468, n2=136
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 338436 468 136 false.
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
    (* Compute the modulo to show it is not 0 *)
    (* (453 * 468) mod (338436 * 136) reduces to 212004 *)
    vm_compute in H_mod.
    (* 212004 = 0 is a contradiction *)
    inversion H_mod.
Qed.