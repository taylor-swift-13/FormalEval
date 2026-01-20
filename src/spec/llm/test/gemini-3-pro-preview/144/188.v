Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/9"; "11/9"] -> x1=11, x2=9, n1=11, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 9 11 9 false.
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
    (* Simplify algebraic expressions: (11 * 11) mod (9 * 9) *)
    (* 11 * 11 = 121 *)
    (* 9 * 9 = 81 *)
    (* 121 mod 81 = 40 *)
    (* H_mod becomes 40 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.