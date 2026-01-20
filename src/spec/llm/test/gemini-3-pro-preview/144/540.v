Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["83/8"; "357/55"] -> x1=83, x2=8, n1=357, n2=55
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 83 8 357 55 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (83 * 357) mod (8 * 55) *)
    (* 83 * 357 = 29631 *)
    (* 8 * 55 = 440 *)
    (* 29631 mod 440 = 151 *)
    (* 151 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.