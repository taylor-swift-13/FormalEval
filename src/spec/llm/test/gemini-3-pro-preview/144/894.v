Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["116853/58"; "16853/58"] -> x1=116853, x2=58, n1=16853, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 116853 58 16853 58 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the algebraic expression: (116853 * 16853) mod (58 * 58) *)
    (* This computes to a non-zero value, so H_mod (n = 0) is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.