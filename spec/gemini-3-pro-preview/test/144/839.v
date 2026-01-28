Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/2991"; "380/241"] -> x1=857, x2=2991, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 857 2991 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    (* We need to show that if mod = 0, then false = true (contradiction),
       which implies mod <> 0. *)
    intros H_mod.
    (* Compute the actual values to show the contradiction *)
    vm_compute in H_mod.
    (* H_mod simplifies to 325660 = 0, which is false *)
    discriminate H_mod.
Qed.