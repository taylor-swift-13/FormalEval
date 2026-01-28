Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["6467/7636"; "111/9"] -> x1=6467, x2=7636, n1=111, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 6467 7636 111 9 false.
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
    (* Compute the modulo: (6467 * 111) mod (7636 * 9) *)
    vm_compute in H_mod.
    (* H_mod reduces to 30597 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.