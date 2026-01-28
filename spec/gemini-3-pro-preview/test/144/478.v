Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/521217"; "23/521217"] -> x1=23, x2=521217, n1=23, n2=521217
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 521217 23 521217 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo arithmetic: (23 * 23) mod (521217 * 521217) *)
    (* This results in 529 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.