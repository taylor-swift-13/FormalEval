Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/9"; "5597/25757775"] -> x1=11, x2=9, n1=5597, n2=25757775
   Output: false -> result=false
*)
Example test_simplify : simplify_spec 11 9 5597 25757775 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (11 * 5597) mod (9 * 25757775) *)
    (* 11 * 5597 = 61567 *)
    (* 9 * 25757775 = 231819975 *)
    (* 61567 mod 231819975 = 61567 *)
    (* H_mod becomes 61567 = 0, which is false *)
    compute in H_mod.
    discriminate.
Qed.