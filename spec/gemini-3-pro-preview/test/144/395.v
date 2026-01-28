Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163/538"; "163/538"] -> x1=163, x2=538, n1=163, n2=538
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 163 538 163 538 false.
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
    (* Compute values to show contradiction: 
       163 * 163 = 26569
       538 * 538 = 289444
       26569 mod 289444 = 26569 <> 0 
    *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.