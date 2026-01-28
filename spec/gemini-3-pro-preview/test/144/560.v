Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/7"; "711/77"] -> x1=11, x2=7, n1=711, n2=77
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 7 711 77 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11 * 711) mod (7 * 77) *)
    (* 11 * 711 = 7821 *)
    (* 7 * 77 = 539 *)
    (* 7821 mod 539 = 275 *)
    (* 275 <> 0, so H_mod is False *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.