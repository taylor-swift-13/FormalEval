Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["17/15"; "15/1117"] -> x1=17, x2=15, n1=15, n2=1117
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 17 15 15 1117 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (17 * 15) mod (15 * 1117) *)
    (* 17 * 15 = 255 *)
    (* 15 * 1117 = 16755 *)
    (* 255 mod 16755 = 255 *)
    (* H_mod : 255 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.