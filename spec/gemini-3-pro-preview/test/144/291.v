Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1111/7"; "5597/2757775"] -> x1=1111, x2=7, n1=5597, n2=2757775
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1111 7 5597 2757775 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (1111 * 5597) mod (7 * 2757775) *)
    (* 1111 * 5597 = 6218267 *)
    (* 7 * 2757775 = 19304425 *)
    (* 6218267 mod 19304425 = 6218267 (since numerator < denominator) *)
    (* 6218267 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.