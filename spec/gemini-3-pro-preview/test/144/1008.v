Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/5725"; "380/2401"] -> x1=7, x2=5725, n1=380, n2=2401
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 5725 380 2401 false.
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
    (* Check the modulo calculation *)
    (* (7 * 380) = 2660 *)
    (* (5725 * 2401) = 13745725 *)
    (* 2660 mod 13745725 = 2660 *)
    (* 2660 = 0 is a contradiction *)
    vm_compute in H_mod.
    inversion H_mod.
Qed.