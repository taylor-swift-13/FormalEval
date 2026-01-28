Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/117"; "3880/241"] -> x1=176, x2=117, n1=3880, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 176 117 3880 241 false.
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
    (* Calculate (176 * 3880) mod (117 * 241) *)
    (* (176 * 3880) = 682880 *)
    (* (117 * 241) = 28197 *)
    (* 682880 mod 28197 = 6152 *)
    (* 6152 <> 0, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.