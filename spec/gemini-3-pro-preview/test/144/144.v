Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/9"; "5597/275775"] -> x1=11, x2=9, n1=5597, n2=275775
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 9 5597 275775 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the arithmetic: (11 * 5597) mod (9 * 275775) *)
    vm_compute in H_mod.
    (* H_mod reduces to 61567 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.