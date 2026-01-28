Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4676/76"; "5453/84"] -> x1=4676, x2=76, n1=5453, n2=84
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 4676 76 5453 84 false.
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
    (* (4676 * 5453) mod (76 * 84) evaluates to 532, not 0. *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.