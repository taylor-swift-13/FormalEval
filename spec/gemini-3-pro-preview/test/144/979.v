Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["168553/658"; "8523/522291"] -> x1=168553, x2=658, n1=8523, n2=522291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 168553 658 8523 522291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo to show it is not 0 *)
    vm_compute in H_mod.
    (* 61907307 = 0 is a contradiction *)
    discriminate.
Qed.