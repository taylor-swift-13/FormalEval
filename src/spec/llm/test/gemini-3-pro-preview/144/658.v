Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/117"; "163/558"] -> x1=16, x2=117, n1=163, n2=558
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 16 117 163 558 false.
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
    (* Simplify algebraic expressions: (16 * 163) mod (117 * 558) *)
    (* 16 * 163 = 2608 *)
    (* 117 * 558 = 65286 *)
    (* 2608 mod 65286 = 2608 *)
    (* 2608 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.