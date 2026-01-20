Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/17"; "11/99"] -> x1=111, x2=17, n1=11, n2=99
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 111 17 11 99 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (111 * 11) mod (17 * 99) *)
    (* 111 * 11 = 1221 *)
    (* 17 * 99 = 1683 *)
    (* 1221 mod 1683 = 1221 *)
    (* Hypothesis H_mod becomes 1221 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.