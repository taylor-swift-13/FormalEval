Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453353/3"; "45535/3"] -> x1=453353, x2=3, n1=45535, n2=3
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 453353 3 45535 3 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo expression *)
    vm_compute in H_mod.
    (* H_mod reduces to 2 = 0, which is a contradiction *)
    discriminate.
Qed.