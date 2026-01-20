Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1653/58"; "857/291"] -> x1=1653, x2=58, n1=857, n2=291
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 1653 58 857 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo to show it is not 0 *)
    vm_compute in H_mod.
    (* The hypothesis becomes a contradiction (non-zero constant = 0) *)
    discriminate H_mod.
Qed.