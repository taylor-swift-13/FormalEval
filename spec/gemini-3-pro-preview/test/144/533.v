Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["468/136"; "11/77"] -> x1=468, x2=136, n1=11, n2=77
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 468 136 11 77 false.
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
    (* Simplify algebraic expressions: (468 * 11) mod (136 * 77) *)
    (* 468 * 11 = 5148 *)
    (* 136 * 77 = 10472 *)
    (* 5148 mod 10472 = 5148 *)
    (* 5148 = 0 is impossible *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.