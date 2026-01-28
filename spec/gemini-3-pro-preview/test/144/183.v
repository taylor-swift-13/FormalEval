Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["173/77"; "173/77"] -> x1=173, x2=77, n1=173, n2=77
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 173 77 173 77 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (173 * 173) mod (77 * 77) evaluates to 284 *)
    compute in H_mod.
    (* 284 = 0 is a contradiction *)
    discriminate H_mod.
Qed.