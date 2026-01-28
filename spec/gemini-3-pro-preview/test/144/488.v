Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/17"; "111/17"] -> x1=111, x2=17, n1=111, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 111 17 111 17 false.
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
    (* Calculate (111 * 111) mod (17 * 17) *)
    (* 111 * 111 = 12321 *)
    (* 17 * 17 = 289 *)
    (* 12321 mod 289 = 186 *)
    (* Hypothesis H_mod implies 186 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.