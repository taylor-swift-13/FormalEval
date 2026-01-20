Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1111/17"; "161111/78"] -> x1=1111, x2=17, n1=161111, n2=78
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1111 17 161111 78 false.
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
    (* Simplify algebraic expressions: (1111 * 161111) mod (17 * 78) *)
    (* 1111 * 161111 = 178994321 *)
    (* 17 * 78 = 1326 *)
    (* 178994321 mod 1326 = 233 *)
    (* 233 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.