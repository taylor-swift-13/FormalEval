Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3880/241"; "943/9"] -> x1=3880, x2=241, n1=943, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3880 241 943 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3880 * 943) mod (241 * 9) *)
    (* 3880 * 943 = 3658840 *)
    (* 241 * 9 = 2169 *)
    (* 3658840 mod 2169 = 1906 *)
    (* 1906 <> 0 *)
    compute in H_mod.
    discriminate H_mod.
Qed.