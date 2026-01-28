Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/5291"; "3/8"] -> x1=857, x2=5291, n1=3, n2=8
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 857 5291 3 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (857 * 3) mod (5291 * 8) evaluates to 2571 *)
    (* 2571 = 0 is impossible *)
    vm_compute in H_mod.
    discriminate.
Qed.