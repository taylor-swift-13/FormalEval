Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["37/55"; "37/55"] -> x1=37, x2=55, n1=37, n2=55
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 37 55 37 55 false.
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
    (* Calculate (37 * 37) mod (55 * 55) *)
    (* 37 * 37 = 1369 *)
    (* 55 * 55 = 3025 *)
    (* 1369 mod 3025 = 1369 *)
    (* 1369 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.