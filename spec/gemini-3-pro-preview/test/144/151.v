Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["6467/736"; "468/136"] -> x1=6467, x2=736, n1=468, n2=136
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 6467 736 468 136 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Verify calculation is not 0: 3026556 mod 100096 <> 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.