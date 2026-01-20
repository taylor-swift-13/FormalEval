Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/99"; "453/3384"] -> x1=11, x2=99, n1=453, n2=3384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 99 453 3384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11 * 453) mod (99 * 3384) *)
    (* 11 * 453 = 4983 *)
    (* 99 * 3384 = 335016 *)
    (* 4983 mod 335016 = 4983 *)
    vm_compute in H_mod.
    (* 4983 = 0 is False *)
    inversion H_mod.
Qed.