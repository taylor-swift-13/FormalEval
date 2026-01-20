Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["112/9"; "205/225"] -> x1=112, x2=9, n1=205, n2=225
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 112 9 205 225 false.
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
    (* Compute values: (112 * 205) mod (9 * 225) *)
    (* 22960 mod 2025 = 685 *)
    (* 685 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.