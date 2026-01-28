Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8577/2921"; "8577/291"] -> x1=8577, x2=2921, n1=8577, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8577 2921 8577 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show contradiction from H_mod *)
    (* (8577 * 8577) mod (2921 * 291) = 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 463983 = 0 *)
    discriminate H_mod.
Qed.