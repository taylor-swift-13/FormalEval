Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["233/25"; "38/113"] -> x1=233, x2=25, n1=38, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 233 25 38 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Check algebraic expressions: (233 * 38) mod (25 * 113) *)
    (* 233 * 38 = 8854 *)
    (* 25 * 113 = 2825 *)
    (* 8854 mod 2825 = 379 *)
    (* H_mod becomes 379 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.