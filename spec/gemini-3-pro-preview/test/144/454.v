Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9231/739"; "163/5"] -> x1=9231, x2=739, n1=163, n2=5
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 9231 739 163 5 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (9231 * 163) mod (739 * 5) computes to 788 *)
    (* H_mod becomes 788 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.