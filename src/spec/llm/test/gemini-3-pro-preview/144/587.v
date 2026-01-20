Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["46744/744346"; "4674/744346"] -> x1=46744, x2=744346, n1=4674, n2=744346
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 46744 744346 4674 744346 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* false = true is a contradiction *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    (* (46744 * 4674) mod (744346 * 744346) is not 0, so hypothesis is false *)
    intros H_mod.
    vm_compute in H_mod.
    discriminate H_mod.
Qed.