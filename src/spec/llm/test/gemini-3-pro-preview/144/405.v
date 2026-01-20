Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["77/2"; "3/8"] -> x1=77, x2=2, n1=3, n2=8
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 77 2 3 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (77 * 3) mod (2 * 8) *)
    (* 77 * 3 = 231 *)
    (* 2 * 8 = 16 *)
    (* 231 mod 16 = 7 *)
    (* H_mod becomes 7 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.