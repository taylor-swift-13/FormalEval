Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3803/2"; "7/725"] -> x1=3803, x2=2, n1=7, n2=725
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3803 2 7 725 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3803 * 7) mod (2 * 725) *)
    (* 3803 * 7 = 26621 *)
    (* 2 * 725 = 1450 *)
    (* 26621 mod 1450 = 521 *)
    (* 521 <> 0 *)
    compute in H_mod.
    discriminate.
Qed.