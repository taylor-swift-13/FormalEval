Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/2291"; "38/13"] -> x1=857, x2=2291, n1=38, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 2291 38 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (857 * 38) mod (2291 * 13) *)
    (* 857 * 38 = 32566 *)
    (* 2291 * 13 = 29783 *)
    (* 32566 mod 29783 = 2783 *)
    (* H_mod reduces to 2783 = 0, which is impossible *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.