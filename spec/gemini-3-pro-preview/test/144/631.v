Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/275"; "23/52"] -> x1=597, x2=275, n1=23, n2=52
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 597 275 23 52 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (597 * 23) mod (275 * 52) *)
    vm_compute in H_mod.
    (* H_mod becomes 13731 = 0, which is false *)
    discriminate.
Qed.