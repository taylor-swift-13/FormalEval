Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["138/1113"; "138/1113"] -> x1=138, x2=1113, n1=138, n2=1113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 138 1113 138 1113 false.
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
    (* Simplify algebraic expressions: (138 * 138) mod (1113 * 1113) *)
    (* 138 * 138 = 19044 *)
    (* 1113 * 1113 = 1238769 *)
    (* 19044 mod 1238769 = 19044 *)
    (* 19044 = 0 is a contradiction *)
    vm_compute in H_mod.
    inversion H_mod.
Qed.