Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163/558"; "921/13"] -> x1=163, x2=558, n1=921, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 163 558 921 13 false.
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
    (* Check if (163 * 921) mod (558 * 13) is actually 0 *)
    (* 163 * 921 = 150123 *)
    (* 558 * 13 = 7254 *)
    (* 150123 mod 7254 = 5043 *)
    (* 5043 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.