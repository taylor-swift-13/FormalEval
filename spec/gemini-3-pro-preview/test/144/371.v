Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["455553/384"; "13/77"] -> x1=455553, x2=384, n1=13, n2=77
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 455553 384 13 77 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Verify that (455553 * 13) mod (384 * 77) is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 8589 = 0, which is false *)
    discriminate H_mod.
Qed.