Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/27"; "597/275"] -> x1=597, x2=27, n1=597, n2=275
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 597 27 597 275 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (597 * 597) mod (27 * 275) *)
    (* 597 * 597 = 356409 *)
    (* 27 * 275 = 7425 *)
    (* 356409 mod 7425 = 9 *)
    (* 9 = 0 is False *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.