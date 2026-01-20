Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/384"; "233/52"] -> x1=453, x2=384, n1=233, n2=52
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 384 233 52 false.
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
    (* Calculate modulo: (453 * 233) mod (384 * 52) *)
    (* 105549 mod 19968 = 5709 *)
    (* 5709 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.