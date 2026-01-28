Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2055/25"; "22/3"] -> x1=2055, x2=25, n1=22, n2=3
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2055 25 22 3 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is contradictory *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (2055 * 22) mod (25 * 3) *)
    (* 2055 * 22 = 45210 *)
    (* 25 * 3 = 75 *)
    (* 45210 mod 75 = 60 *)
    (* Hypothesis H_mod implies 60 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.