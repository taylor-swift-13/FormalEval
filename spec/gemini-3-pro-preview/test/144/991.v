Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/17"; "9291/739"] -> x1=16, x2=17, n1=9291, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16 17 9291 739 false.
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
    (* Calculate modulo: (16 * 9291) mod (17 * 739) *)
    (* 148656 mod 12563 = 10463 *)
    (* 10463 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.