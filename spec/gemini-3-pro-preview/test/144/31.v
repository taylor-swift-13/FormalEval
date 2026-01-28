Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["12/9"; "13/19"] -> x1=12, x2=9, n1=13, n2=19
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 12 9 13 19 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate the actual modulo value *)
    (* 12 * 13 = 156 *)
    (* 9 * 19 = 171 *)
    (* 156 mod 171 = 156 *)
    assert (H_calc: (12 * 13) mod (9 * 19) = 156) by reflexivity.
    rewrite H_calc in H_mod.
    (* H_mod is now 156 = 0, a contradiction *)
    discriminate H_mod.
Qed.