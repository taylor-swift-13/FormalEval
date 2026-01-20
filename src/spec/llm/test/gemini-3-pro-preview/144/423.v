Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/17"; "176/9"] -> x1=16, x2=17, n1=176, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16 17 176 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (16 * 176) mod (17 * 9) *)
    (* 16 * 176 = 2816 *)
    (* 17 * 9 = 153 *)
    (* 2816 mod 153 = 62 *)
    (* H_mod implies 62 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.