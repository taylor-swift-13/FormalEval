Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/275"; "23/522"] -> x1=597, x2=275, n1=23, n2=522
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 597 275 23 522 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that mod = 0 implies a contradiction (since result is false) *)
    (* (597 * 23) mod (275 * 522) evaluates to 13731 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.