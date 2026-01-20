Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/291"; "23/71"] -> x1=857, x2=291, n1=23, n2=71
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 291 23 71 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo: (857 * 23) mod (291 * 71) = 19711 mod 20661 = 19711 *)
    (* 19711 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.