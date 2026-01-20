Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/252"; "99/100"] -> x1=23, x2=252, n1=99, n2=100
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 23 252 99 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (23 * 99) mod (252 * 100) *)
    (* 23 * 99 = 2277 *)
    (* 252 * 100 = 25200 *)
    (* 2277 mod 25200 = 2277 *)
    (* H_mod becomes 2277 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.