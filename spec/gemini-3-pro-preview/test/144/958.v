Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/77"; "3/13"] -> x1=11, x2=77, n1=3, n2=13
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 11 77 3 13 false.
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
    (* Simplify algebraic expressions: (11 * 3) mod (77 * 13) *)
    (* 11 * 3 = 33 *)
    (* 77 * 13 = 1001 *)
    (* 33 mod 1001 = 33 *)
    (* H_mod becomes 33 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.