Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["5597/275775"; "163/58"] -> x1=5597, x2=275775, n1=163, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 5597 275775 163 58 false.
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
    (* (5597 * 163) mod (275775 * 58) reduces to 912311 *)
    (* 912311 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.