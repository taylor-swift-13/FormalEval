Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/291"; "45535/3"] -> x1=857, x2=291, n1=45535, n2=3
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 291 45535 3 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (857 * 45535) mod (291 * 3) *)
    vm_compute in H_mod.
    (* 395 = 0 is a contradiction *)
    discriminate H_mod.
Qed.