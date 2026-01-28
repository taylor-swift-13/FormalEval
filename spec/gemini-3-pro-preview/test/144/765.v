Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/291"; "8523/5922291"] -> x1=857, x2=291, n1=8523, n2=5922291
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 857 291 8523 5922291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (857 * 8523) mod (291 * 5922291) *)
    (* 857 * 8523 = 7304211 *)
    (* 291 * 5922291 = 1723386681 *)
    (* 7304211 mod 1723386681 = 7304211 *)
    (* 7304211 <> 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.