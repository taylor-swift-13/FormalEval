Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/522"; "11/19"] -> x1=23, x2=522, n1=11, n2=19
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 522 11 19 false.
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
    (* Calculate modulo: (23 * 11) mod (522 * 19) *)
    (* 23 * 11 = 253 *)
    (* 522 * 19 = 9918 *)
    (* 253 mod 9918 = 253 *)
    (* Hypothesis H_mod becomes 253 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.