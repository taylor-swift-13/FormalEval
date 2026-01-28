Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["380/241"; "943/9"] -> x1=380, x2=241, n1=943, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 380 241 943 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (380 * 943) mod (241 * 9) *)
    (* 380 * 943 = 358340 *)
    (* 241 * 9 = 2169 *)
    (* 358340 mod 2169 = 455 *)
    assert (H_calc: (380 * 943) mod (241 * 9) = 455) by reflexivity.
    rewrite H_calc in H_mod.
    (* 455 = 0 is false *)
    discriminate H_mod.
Qed.