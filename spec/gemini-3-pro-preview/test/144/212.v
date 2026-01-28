Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9943/29"; "8/13"] -> x1=9943, x2=29, n1=8, n2=13
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 9943 29 8 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (9943 * 8) mod (29 * 13) *)
    (* 9943 * 8 = 79544 *)
    (* 29 * 13 = 377 *)
    (* 79544 mod 377 = 374 *)
    (* H_mod becomes 374 = 0, which is false *)
    vm_compute in H_mod.
    discriminate.
Qed.