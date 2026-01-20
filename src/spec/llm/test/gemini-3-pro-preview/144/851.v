Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/2975"; "380/241"] -> x1=597, x2=2975, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 597 2975 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* false = true is a contradiction *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (597 * 380) mod (2975 * 241) *)
    (* 597 * 380 = 226860 *)
    (* 2975 * 241 = 716975 *)
    (* 226860 mod 716975 = 226860 <> 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.