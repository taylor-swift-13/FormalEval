Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["133/19"; "19/13"] -> x1=133, x2=19, n1=19, n2=13
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 133 19 19 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (133 * 19) mod (19 * 13) *)
    (* 2527 mod 247 = 57 *)
    (* H_mod implies 57 = 0, which is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.