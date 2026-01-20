Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1857/7291"; "1857/7291"] -> x1=1857, x2=7291, n1=1857, n2=7291
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 1857 7291 1857 7291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (1857 * 1857) mod (7291 * 7291) *)
    (* Since 0 < 1857 < 7291, the square is less than the modulus, so remainder is non-zero *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.