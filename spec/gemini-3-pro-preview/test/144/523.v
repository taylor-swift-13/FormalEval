Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/5291"; "453/3384"] -> x1=857, x2=5291, n1=453, n2=3384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 5291 453 3384 false.
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
    (* Evaluate the algebraic expressions *)
    (* (857 * 453) mod (5291 * 3384) *)
    vm_compute in H_mod.
    (* H_mod reduces to 388221 = 0, which is false *)
    discriminate.
Qed.