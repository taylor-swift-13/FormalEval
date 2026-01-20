Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["12/9"; "17/15"] -> x1=12, x2=9, n1=17, n2=15
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 12 9 17 15 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H_contra.
    discriminate H_contra.
  - (* Right to Left: ... -> false = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (12 * 17) mod (9 * 15) *)
    vm_compute in H_mod.
    (* Reduced to 69 = 0, which is false *)
    discriminate H_mod.
Qed.