Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/3"; "7/255"] -> x1=2, x2=3, n1=7, n2=255
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2 3 7 255 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (2 * 7) mod (3 * 255) *)
    (* 2 * 7 = 14 *)
    (* 3 * 255 = 765 *)
    (* 14 mod 765 = 14 *)
    (* H_mod becomes 14 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.