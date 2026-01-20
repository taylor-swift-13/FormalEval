Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3803/2"; "23/52"] -> x1=3803, x2=2, n1=23, n2=52
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3803 2 23 52 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3803 * 23) mod (2 * 52) *)
    (* 3803 * 23 = 87469 *)
    (* 2 * 52 = 104 *)
    (* 87469 mod 104 = 5 *)
    (* 5 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.