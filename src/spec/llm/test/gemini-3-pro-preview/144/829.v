Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/21"; "3/13"] -> x1=857, x2=21, n1=3, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 21 3 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (857 * 3) mod (21 * 13) *)
    (* This computes to 114 = 0, which is false *)
    vm_compute in H_mod.
    discriminate.
Qed.