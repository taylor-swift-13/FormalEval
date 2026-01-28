Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/9291"; "23/5"] -> x1=857, x2=9291, n1=23, n2=5
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 9291 23 5 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (857 * 23) mod (9291 * 5) *)
    (* 857 * 23 = 19711 *)
    (* 9291 * 5 = 46455 *)
    (* 19711 mod 46455 = 19711 *)
    (* Hypothesis H_mod says 19711 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.