Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2055/25"; "205/25"] -> x1=2055, x2=25, n1=205, n2=25
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2055 25 205 25 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (2055 * 205) mod (25 * 25) *)
    (* 2055 * 205 = 421275 *)
    (* 25 * 25 = 625 *)
    (* 421275 mod 625 = 25 *)
    (* H_mod becomes 25 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.