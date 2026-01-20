Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9231/739"; "9221/739"] -> x1=9231, x2=739, n1=9221, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9231 739 9221 739 false.
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
    (* We need to show that the modulo is not 0, hence H_mod is false *)
    vm_compute in H_mod.
    (* H_mod reduces to 470296 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.