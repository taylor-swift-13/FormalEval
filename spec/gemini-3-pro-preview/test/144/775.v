Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163311/9"; "943/9"] -> x1=163311, x2=9, n1=943, n2=9
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 163311 9 943 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate algebraic expressions: (163311 * 943) mod (9 * 9) *)
    vm_compute in H_mod.
    (* 51 = 0 is false *)
    discriminate H_mod.
Qed.