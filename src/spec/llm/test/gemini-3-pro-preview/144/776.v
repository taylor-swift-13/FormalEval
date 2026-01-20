Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/9"; "2/252"] -> x1=111, x2=9, n1=2, n2=252
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 111 9 2 252 false.
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
    (* Simplify algebraic expressions: (111 * 2) mod (9 * 252) *)
    (* 111 * 2 = 222 *)
    (* 9 * 252 = 2268 *)
    (* 222 mod 2268 = 222 *)
    (* Hypothesis H_mod becomes 222 = 0, which is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.