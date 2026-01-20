Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4367/736"; "233/52"] -> x1=4367, x2=736, n1=233, n2=52
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 4367 736 233 52 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* result is false, so false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the arithmetic expression in the hypothesis *)
    vm_compute in H_mod.
    (* H_mod reduces to 22439 = 0, which is false *)
    discriminate H_mod.
Qed.