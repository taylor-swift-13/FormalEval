Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["30802/24"; "921/739"] -> x1=30802, x2=24, n1=921, n2=739
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 30802 24 921 739 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (30802 * 921) mod (24 * 739) *)
    vm_compute in H_mod.
    (* We get 8778 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.