Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["19/13"; "19/3"] -> x1=19, x2=13, n1=19, n2=3
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 19 13 19 3 false.
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
    (* (19 * 19) mod (13 * 3) = 361 mod 39 = 10 *)
    (* 10 = 0 is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.