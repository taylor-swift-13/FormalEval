Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1111/7"; "468/136"] -> x1=1111, x2=7, n1=468, n2=136
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1111 7 468 136 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    (* We need to show that if mod = 0, then false = true.
       Since false = true is impossible, we must show mod <> 0. *)
    intros H_mod.
    (* Compute the values:
       1111 * 468 = 519948
       7 * 136 = 952
       519948 mod 952 = 156
       So H_mod asserts 156 = 0, which is false. *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.