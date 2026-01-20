Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/9"; "176/17"] -> x1=11, x2=9, n1=176, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 9 176 17 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11 * 176) mod (9 * 17) *)
    (* 11 * 176 = 1936 *)
    (* 9 * 17 = 153 *)
    (* 1936 mod 153 = 100 *)
    (* H_mod implies 100 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.