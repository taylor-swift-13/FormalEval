Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/717"; "453/38"] -> x1=176, x2=717, n1=453, n2=38
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 176 717 453 38 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (176 * 453) mod (717 * 38) *)
    (* 176 * 453 = 79728 *)
    (* 717 * 38 = 27246 *)
    (* 79728 mod 27246 = 25236 *)
    (* 25236 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.