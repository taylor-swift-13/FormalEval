Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/5"; "4674/736"] -> x1=3, x2=5, n1=4674, n2=736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3 5 4674 736 false.
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
    (* Simplify algebraic expressions: (3 * 4674) mod (5 * 736) *)
    (* 3 * 4674 = 14022 *)
    (* 5 * 736 = 3680 *)
    (* 14022 mod 3680 = 2982 *)
    (* 2982 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.