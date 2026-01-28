Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/384"; "453/38"] -> x1=453, x2=384, n1=453, n2=38
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 384 453 38 false.
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
    (* Evaluate the modulo: (453 * 453) mod (384 * 38) *)
    (* 205209 mod 14592 = 921 *)
    vm_compute in H_mod.
    (* 921 = 0 is a contradiction *)
    discriminate H_mod.
Qed.