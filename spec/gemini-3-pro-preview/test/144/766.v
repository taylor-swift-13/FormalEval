Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["999/100"; "943/9"] -> x1=999, x2=100, n1=943, n2=9
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 999 100 943 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H_contra.
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Evaluate the arithmetic expression in H_mod *)
    (* (999 * 943) mod (100 * 9) -> 942057 mod 900 -> 657 *)
    vm_compute in H_mod.
    (* H_mod becomes 657 = 0, which is false *)
    discriminate H_mod.
Qed.