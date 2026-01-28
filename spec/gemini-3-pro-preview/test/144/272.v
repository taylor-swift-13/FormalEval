Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["5597/25757775"; "5597/2757775"] -> x1=5597, x2=25757775, n1=5597, n2=2757775
   Output: false -> result=false
*)
Example test_simplify_case : simplify_spec 5597 25757775 5597 2757775 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo arithmetic to show it is non-zero *)
    vm_compute in H_mod.
    (* H_mod becomes 31326409 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.