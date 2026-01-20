Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/117"; "23/5"] -> x1=16, x2=117, n1=23, n2=5
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 16 117 23 5 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (16 * 23) mod (117 * 5) *)
    (* 16 * 23 = 368 *)
    (* 117 * 5 = 585 *)
    (* 368 mod 585 = 368 *)
    (* Hypothesis becomes 368 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.