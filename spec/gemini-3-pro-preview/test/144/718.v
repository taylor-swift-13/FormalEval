Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/291"; "1683/58"] -> x1=857, x2=291, n1=1683, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 291 1683 58 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (857 * 1683) mod (291 * 58) *)
    (* 857 * 1683 = 1442331 *)
    (* 291 * 58 = 16878 *)
    (* 1442331 mod 16878 = 7701 *)
    (* 7701 <> 0, so H_mod is False *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.