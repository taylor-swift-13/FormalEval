Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9176/9"; "7/5"] -> x1=9176, x2=9, n1=7, n2=5
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9176 9 7 5 false.
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
    (* Simplify algebraic expressions: (9176 * 7) mod (9 * 5) *)
    (* (9176 * 7) = 64232 *)
    (* (9 * 5) = 45 *)
    (* 64232 mod 45 = 17 *)
    (* H_mod implies 17 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.