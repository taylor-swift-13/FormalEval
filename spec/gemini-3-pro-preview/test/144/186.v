Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/99"; "921/739"] -> x1=11, x2=99, n1=921, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 99 921 739 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_contra.
    (* false = true is a contradiction *)
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (11 * 921) mod (99 * 739) *)
    (* 10131 mod 73161 = 10131 *)
    (* H_mod implies 10131 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.