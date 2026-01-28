Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["30802/24"; "3080/241"] -> x1=30802, x2=24, n1=3080, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 30802 24 3080 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that (30802 * 3080) mod (24 * 241) = 0 is false *)
    vm_compute in H_mod.
    (* H_mod reduces to 992 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.