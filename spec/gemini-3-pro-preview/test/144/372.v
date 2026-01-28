Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["5597/2755775"; "3180/241"] -> x1=5597, x2=2755775, n1=3180, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 5597 2755775 3180 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Compute the modulo value in the hypothesis *)
    vm_compute in H_mod.
    (* H_mod now states 17798460 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.