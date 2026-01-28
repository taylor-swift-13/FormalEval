Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/9"; "6176/9"] -> x1=176, x2=9, n1=6176, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 176 9 6176 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (176 * 6176) mod (9 * 9) *)
    (* 176 * 6176 = 1086976 *)
    (* 9 * 9 = 81 *)
    (* 1086976 mod 81 = 37 *)
    (* H_mod becomes 37 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.